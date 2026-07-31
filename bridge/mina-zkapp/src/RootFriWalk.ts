import { BbExt } from './FriQueryStep.js';
import { DEPLOYED_KNOBS, FriKnobs } from './FriChallenger.js';
import { rootAirDag } from './RootAirDag.js';
import { BABYBEAR_HASH, HashPrice, LANE_COST, PASTA_HASH } from './CostModel.js';

// ---------------------------------------------------------------------------
// THE ROOT'S FRI WALK AS A SEGMENT LIST — the object the AIR chain's terminal
// seal is braided INTO.
//
// ⚑ WHAT THIS IS FOR. The AIR half is closed at real geometry: seven slices,
// seven processes, all 10,417 DAG nodes and all 1,093 constraints over dregg's
// committed root proof, ending in `airTerminalSeal(dagDigest, digest(acc), 7)` —
// and `acc` is verifier-computable as `Σ_T acc_T · α^(1093 − b_T)`. That seal
// says the AIR's closing equalities hold **at the opened values the chain was
// handed**. It says nothing about whether those opened values are the ones
// dregg committed to. Authenticating them is the FRI walk, and the two halves
// have never been the same chain.
//
// ⚑ AND THE JOIN IS NOT A CONCATENATION. Two chains glued end to end, each
// reading its own copy of the opened values, prove strictly less than either
// looks like it proves: the AIR half folds one set of numbers, the FRI half
// authenticates another, and nothing says they are the same set. The braid is
// therefore built on ONE column commitment. `dagDigest` — the AIR chain's own
// chunked commitment over its 1,602 extension values — is carried across the
// seal into the FRI slices, and every DEEP-quotient term whose `f(z)` the AIR
// legend names is READ OUT OF THOSE CHUNKS rather than witnessed again. A FRI
// half that authenticated different numbers would re-derive a different
// `dagDigest` and the boundary would refuse.
//
// ⚑ WHAT THE AIR LEGEND DOES NOT COVER, MEASURED RATHER THAN ASSUMED. The AIR
// reads only the columns it constrains. Measured against the proof's own opened
// set: **1,748 of the 2,630 opened values (66.5%) are lanes of the AIR chain's
// assignment**, and the other 882 — the main and preprocessed columns the AIR
// never touches, plus all 56 quotient-chunk openings — go under a second,
// FRI-side commitment (`friDigest`). Both are in the boundary; only the first is
// shared with the AIR half, and `planOpenedValues` reports the ratio so the
// claim is a number rather than a word.
//
// ⚑ 2,630, NOT 2,286 — AND THE CORRECTION GOES BOTH WAYS. §3.15 prices the DEEP
// quotient at `940·2 + 175·2 + 7·2·4 = 2,286`. Two things are wrong with that
// and they pull in opposite directions. It omits the PERMUTATION round entirely
// (the root's seven instances carry 64 extension permutation columns = 512
// further base terms, all of them opened at two points). And it assumes every
// matrix is opened at TWO points, which the proof refutes: `Const`, `Public`,
// `recompose` and `expose_claim` reference no next-row main or preprocessed
// value, so those matrices are opened at ζ ALONE. The shape is therefore taken
// from the proof's own `inputRounds` and never derived from a table of widths.
//
// ⚑ THE UNIT OF ACCOUNT IS A SEGMENT, AND A CUT MAY ONLY FALL BETWEEN TWO.
// A slice is a contiguous run of segments, exactly as an AIR slice is a
// contiguous run of DAG nodes. Segments are chosen so that every one of them
// fits inside a step domain with room to spare (the widest is 9,600 rows, a
// 128-column DEEP run) and so that the state crossing a cut is small:
// a challenger sponge, a running Merkle digest, a running fold value, and the
// derived challenges. What does NOT cross is the per-query Merkle data — every
// row, path digest and sibling belongs to exactly one segment, and is
// self-authenticating, because the opening it feeds binds it to a commitment
// that IS in the boundary.
// ---------------------------------------------------------------------------

/** ⚑ THE DEPLOYED HASH'S NUMBERS, KEPT AS NAMES BECAUSE ~40 CALL SITES SPELL
 *  THEM. They are no longer the walk's shape — `WalkHash` below is — and every
 *  one of these is now the `poseidon2-babybear-w16` ROW of that record. Reading
 *  one of these where the walk's own hash is meant is the defect this file's
 *  §1a exists to make impossible. */
export const LANES_PER_DIGEST = 8;
export const EXT_LANES = 4;
export const CHAL_WIDTH = 16;
export const CHAL_RATE = 8;

// ===========================================================================
// 1a. THE HASH AS A SHAPE, not only as a price.
// ===========================================================================

/**
 * **The structural half of a hash choice.**
 *
 * ⚑ WHY THIS IS A SECOND RECORD AND NOT MORE FIELDS ON `WalkPrice`. `WalkPrice`
 * says what a hash COSTS: swap it and every `rows` figure moves and nothing else
 * does. This says what SHAPE it MAKES: the digest is 8 lanes or 1, the leaf
 * sponge eats 8 lanes a permutation or 16 and carries 16 lanes of state or 3.
 * Those reach the LANE TABLE (a commitment is `digestLanes` lanes, not eight),
 * the SLOT LAYOUT (the `cur`, `inj` and `sponge` registers), the SEGMENT LIST
 * (`ceil(width / spongeRate)` sponge blocks), the AUX WIDTHS (a Merkle sibling
 * is `digestLanes` lanes) and the EXECUTOR. A price table alone cannot move any
 * of them, which is exactly the gap `priceForSuite` left open and this closes:
 * pricing is not execution.
 *
 * ⚑ AND `transcript` IS A REFUSAL, NOT A FLAG. See `segmentWalk`.
 */
export type WalkHash = {
  /** The `MerkleSuite.name` this describes. */
  name: string;
  /** Lanes in one MMCS digest — 8 BabyBear, 1 Pasta. */
  digestLanes: number;
  /** Lanes the leaf sponge absorbs per permutation — 8 BabyBear, 16 Pasta. */
  spongeRate: number;
  /** Lanes the leaf sponge's running state occupies across a cut — 16, 3. */
  spongeStateLanes: number;
  /** Lanes the CHALLENGER's running state occupies across a cut — 16, 3. */
  chalStateLanes: number;
  /** Lanes absorbed per challenger permutation — 8 BabyBear, 16 Pasta. */
  chalAbsorbRate: number;
  /** Challenges one challenger permutation makes available — 8 BabyBear
   *  (`sponge[..8]`), 14 Pasta (2 rate cells x 7 squeezed limbs). */
  chalSqueeze: number;
  /**
   * ⚑ WHAT A DIGEST LANE **IS**, which is not the same question as how many of
   * them there are.
   *
   * `digestLanes` says a commitment occupies eight lanes or one. This says what
   * lives in one: a BabyBear lane, canonical below `p_BabyBear = 2^31 − 1`, or a
   * NATIVE Pasta field element, which is every `Field` and therefore bounded by
   * nothing. The lane table is otherwise homogeneous — it puts
   * `canonicalLane(l, 2^31 − 1)` on every lane it commits — and a Pasta digest
   * canonicalised as a BabyBear lane refuses EVERY honest proof, because a
   * 255-bit digest is not `< 2^31`.
   *
   * So `FriLaneTable.kinds` and `SlotLayout.kinds` are per-entry vectors driven
   * by this field, and `chunkedCommitment` range-checks a lane only when its
   * kind says the check is meaningful. That is the second of the two blockers
   * `assertLanesAreBabyBear` used to name; it is closed, and the assertion is
   * gone.
   */
  digestKind: 'babybear-lanes' | 'native-field';
  /**
   * ⚑ WHETHER `segmentWalk` MODELS AND `runSegments` EXECUTES THIS HASH'S
   * TRANSCRIPT — and today exactly one hash does.
   *
   * The Merkle half of a hash swap is a substitution: `compress`, `condSwap`,
   * a digest width, a sponge rate. The TRANSCRIPT half is a different STATE
   * MACHINE. `DuplexChallenger<BabyBear, 16, 8>` absorbs and squeezes in one
   * field; `MultiField32Challenger<BabyBear, PastaFp, _, 3, 2>` PACKS eight
   * BabyBear lanes into a Pasta cell to absorb, SPLITS a Pasta cell into seven
   * canonical limbs to squeeze, absorbs a DIGEST natively after flushing the
   * pending base buffer, adds a LENGTH TAG into the capacity, and pops its
   * squeeze queue from the BACK. `segmentWalk`'s emitter models the first and
   * `runSegments` executes it inline; neither knows the second.
   *
   * ⚠ AND THERE IS NO ORACLE FOR THE SECOND ONE TODAY, which is why this is a
   * refusal rather than a lane's afternoon. `RootConsume.rehash` re-commits the
   * root's MMCS digests under a suite — so the Merkle half of a Pasta walk has
   * a twin to check against — but it does NOT re-derive the transcript, and
   * `ROOT_CHALLENGE_STATUS` says the root path CARRIES its challenges. dregg
   * mints no Pasta-hashed root, so a Pasta preamble written here would have
   * nothing to be wrong against: it would compile, prove, and be about a
   * protocol nobody runs. That is the exact shape this directory's own record
   * says its cheap differentials keep catching, so the walk REFUSES BY NAME
   * instead.
   *
   * ⚑ AND THERE IS A THIRD VALUE, WHICH IS THE HONEST ANSWER RATHER THAN A
   * WEAKER REFUSAL. `carried` says: this walk does not derive its transcript at
   * all — FRI's α, the sixteen βs and the nineteen query indices are COMMITTED
   * LANES read into their slots under `friDigest`, exactly as
   * `ROOT_CHALLENGE_STATUS` says the root path already reads them and exactly
   * as the consumer (`DreggProofVerify` + `RootConsume`, `deriveChallenges:
   * false`) already consumes them at BOTH hashes. It is §3.14 residual 1, named,
   * and it is NOT a new hole: the deployed sliced chain's own entering state is
   * a witness too, one permutation earlier in the same argument.
   *
   * What `carried` is NOT is a Pasta preamble. Writing one would mean writing
   * `MultiField32Challenger` into the emitter with no object to be wrong
   * against, and every downstream figure would then be a measurement of a
   * protocol nobody runs. The choice here is between a stated residual and an
   * invented oracle, and the residual is the one that is true.
   *
   * ⚠ WHAT A `carried` WALK THEREFORE DOES NOT SUPPORT: a preamble. `preamble`
   * and `carried` together is refused below, because the preamble IS the
   * derivation this value says is absent.
   */
  transcript: 'implemented' | 'carried' | 'unimplemented';
};

/** The deployed hash's shape — `Poseidon2BabyBear<16>` emulated in Pasta. */
export const BABYBEAR_WALK_HASH: WalkHash = {
  name: 'poseidon2-babybear-w16',
  digestLanes: 8,
  spongeRate: 8,
  spongeStateLanes: 16,
  chalStateLanes: 16,
  chalAbsorbRate: 8,
  chalSqueeze: 8,
  digestKind: 'babybear-lanes',
  transcript: 'implemented',
};

/** `DreggMinaConfig`'s shape — kimchi's own Poseidon over Pasta `Fp`. Every
 *  number here is `PastaMmcs`'/`PastaChallenger`'s, and the two are checked
 *  against each other by `assertWalkHashMatchesSuite`. */
export const PASTA_WALK_HASH: WalkHash = {
  name: 'mina-poseidon-pasta',
  digestLanes: 1,
  spongeRate: 16,
  spongeStateLanes: 3,
  chalStateLanes: 3,
  chalAbsorbRate: 16,
  chalSqueeze: 14,
  digestKind: 'native-field',
  //  ⚑ CARRIED, AND THAT IS THE ANSWER RATHER THAN A DEFERRAL — see
  //  `WalkHash.transcript`. The root path carries its challenges today at BOTH
  //  hashes; a Pasta preamble would be a model of a protocol nobody runs.
  transcript: 'carried',
};

/** The walk's shape for a hash suite, BY THE SUITE'S OWN NAME — the same
 *  refusal `priceForSuite` and `suiteByName` make, for the same reason. */
export function walkHashForSuite(name: string): WalkHash {
  switch (name) {
    case 'poseidon2-babybear-w16':
      return BABYBEAR_WALK_HASH;
    case 'mina-poseidon-pasta':
      return PASTA_WALK_HASH;
    default:
      throw new Error(
        `no walk SHAPE for hash suite '${name}' — a proof minted under a config nobody has ` +
          'measured must be refused by NAME here, not shaped like whichever hash was the default',
      );
  }
}

/**
 * Require a `WalkHash` and the `MerkleSuite` it claims to describe to agree.
 *
 * ⚑ TWO NUMBERINGS OF ONE OBJECT IS THE SHAPE THAT DRIFTS — the same reason
 * `assertPreambleSealLanes` exists. The suite owns `digestElems` and its sponge
 * stream owns the rate and the state width; this checks the record repeats them
 * rather than inventing them, so a hash whose sponge is re-tuned cannot leave a
 * stale walk shape behind.
 */
export function assertWalkHashMatchesSuite(
  hash: WalkHash,
  suite: {
    name: string;
    digestElems: number;
    spongeStream: { rate: number; stateLanes: number };
    laneCheckIsFree?: boolean;
  },
) {
  const mism: string[] = [];
  if (hash.name !== suite.name) mism.push(`name ${hash.name} vs ${suite.name}`);
  //  ⚑ THE LANE KIND IS THE SUITE'S OWN `laneCheckIsFree`, RESTATED — and a
  //  restatement that is not checked is the drift this function exists for. A
  //  digest needs no range check exactly when the hash field IS the circuit's
  //  field, which is exactly when its lanes are native.
  if (suite.laneCheckIsFree !== undefined && (hash.digestKind === 'native-field') !== suite.laneCheckIsFree)
    mism.push(
      `digestKind ${hash.digestKind} vs laneCheckIsFree ${suite.laneCheckIsFree}`,
    );
  if (hash.digestLanes !== suite.digestElems)
    mism.push(`digestLanes ${hash.digestLanes} vs digestElems ${suite.digestElems}`);
  if (hash.spongeRate !== suite.spongeStream.rate)
    mism.push(`spongeRate ${hash.spongeRate} vs spongeStream.rate ${suite.spongeStream.rate}`);
  if (hash.spongeStateLanes !== suite.spongeStream.stateLanes)
    mism.push(
      `spongeStateLanes ${hash.spongeStateLanes} vs spongeStream.stateLanes ${suite.spongeStream.stateLanes}`,
    );
  if (mism.length)
    throw new Error(
      `the walk shape and the hash suite disagree — ${mism.join('; ')}. One object, one set of ` +
        'numbers; a walk built at a shape its own suite does not have is a walk over a different hash.',
    );
}

// ===========================================================================
// 1. Measured unit prices. Every one of these is a `getRows()` figure from a
//    committed leg, not an estimate; the § is where it was taken.
// ===========================================================================

/**
 * The unit prices a walk is costed at.
 *
 * ⚑ THE HASH TERMS ARE A PARAMETER AND THE ARITHMETIC TERMS ARE NOT, and that
 * split IS `MINA-FACING-TERMINAL-OPTIONS`'s whole thesis: `perm`,
 * `merkleLevel`, `merkleInject` and `spongeRate` are properties of WHICH HASH
 * the proof commits with; `horner`, `foldRow`, `rollIn`, `extMul`, `extAdd`,
 * `extInverse`, `descent` and `witnessLane` are BabyBear extension arithmetic
 * and range checks, which no hash choice touches.
 *
 * ⚑ EVERY FIGURE IS OWNED BY `src/CostModel.ts` OR CITED TO ITS LEG HERE. The
 * hash and lane prices are imported rather than restated — they were restated
 * in four places and disagreed in three of them.
 */
export type WalkPrice = {
  perm: number;
  merkleLevel: number;
  merkleInject: number;
  spongeRate: number;
  horner: number;
  foldRow: number;
  rollIn: number;
  extMul: number;
  extAdd: number;
  extInverse: number;
  witnessLane: number;
  descent: number;
};

/** The arithmetic half — hash-independent, so it is shared by every price
 *  table a walk can be costed at. */
export const ARITH_PRICE = {
  /** One extension Horner step `acc ← acc·α + v` (§3.14, MEASURED 49). */
  horner: 49,
  /** One arity-2 `fold_row` (§3.14, MEASURED 150). */
  foldRow: 150,
  /** One reduced-opening roll-in: `folded += β² · ro` (§3.13, MEASURED 88). */
  rollIn: 88,
  extMul: 31,
  extAdd: 19,
  /** `extInverse`: witness 4 lanes, one `extMul`, four canonical comparisons. */
  extInverse: 88,
  /** EMITTED rows to witness and range-check ONE carried lane — a RANGE CHECK,
   *  and therefore hash-independent. Owned by `CostModel.LANE_COST`, which also
   *  carries the reconciliation against §3.20's two bulk slopes. */
  witnessLane: LANE_COST.witnessPerLane,
  /** The coset descent `x ← ±x²`. */
  descent: 20,
} as const;

/** Price a walk at a given hash. */
export const priceAt = (h: HashPrice): WalkPrice => ({
  perm: h.perm,
  merkleLevel: h.merkleLevel,
  merkleInject: h.merkleInject,
  spongeRate: h.spongeRate,
  ...ARITH_PRICE,
});

/** The DEPLOYED price table — the root as it commits today, Poseidon2 over
 *  BabyBear, emulated in a Pasta circuit. */
export const PRICE: WalkPrice = priceAt(BABYBEAR_HASH);

/**
 * The price table for a hash suite, BY THE SUITE'S OWN NAME.
 *
 * ⚑ THE HALF-CLOSED GAP THIS IS THE CLOSED HALF OF. This walk is the
 * real-geometry model — four PCS rounds, five heights, the mixed-height
 * injection schedule — and it priced at `BABYBEAR_HASH` and nothing else, while
 * `PASTA_HASH` sat in `CostModel.ts` used by a comment and by
 * `cost-model-gate`'s own re-derivation. A model that can only be priced at one
 * hash is a model of one hash.
 *
 * ⚑ AND THE CONSTANTS ARE IMPORTED, NEVER RE-DERIVED. `CostModel.ts` is the
 * single owner and `npm run cost-gate` reds on a second home; this maps a name
 * to the owner's row and does no arithmetic of its own.
 *
 * ⚠ WHAT IS STILL BABYBEAR-ONLY, SAID HERE BECAUSE THIS IS WHERE A READER WILL
 * LOOK. Pricing is not execution. `RootFriSlice`'s segment executor still calls
 * `compressBB`/`condSwap` directly and its state slots are eight lanes wide
 * (`LANES_PER_DIGEST`), so the SLICED chain — the braid and the uniform walk —
 * runs the deployed hash whatever this returns. The path that is BOTH
 * four-round AND hash-agnostic is the consumer: `DreggProofVerify` +
 * `RootConsume`, measured at both hashes by `npm run root-consume-rows`. That is
 * the merge; this function is the model catching up to it, and the slice
 * executor's digest width is the remaining item.
 */
export function priceForSuite(name: string): WalkPrice {
  switch (name) {
    case 'poseidon2-babybear-w16':
      return priceAt(BABYBEAR_HASH);
    case 'mina-poseidon-pasta':
      return priceAt(PASTA_HASH);
    default:
      throw new Error(
        `no walk price for hash suite '${name}' — a proof minted under a config nobody has ` +
          'measured must be refused by NAME here, not priced at whichever table was the default',
      );
  }
}

// ===========================================================================
// 2. The shape — the root's PCS rounds, read off the committed proof.
// ===========================================================================

export type MatrixSpec = {
  /** Batch-STARK instance index. */
  instance: number;
  name: string;
  /** `degree_bits + log_blowup`. */
  logHeight: number;
  /** BASE columns committed for this matrix (an extension column is 4). */
  width: number;
  /** Out-of-domain points this matrix is opened at (2 for ζ and g·ζ, 1 for a
   *  quotient chunk). */
  numPoints: number;
};

export type RoundSpec = {
  name: 'main' | 'quotient_chunk' | 'preprocessed' | 'permutation';
  matrices: MatrixSpec[];
};

export type FriShape = {
  knobs: FriKnobs;
  rounds: RoundSpec[];
  /** Distinct input-matrix log heights, DESCENDING. The DEEP quotient keys its
   *  accumulator by these and the roll-in schedule is a function of them. */
  heights: number[];
};

/** `circuit-prove/src/bin/root_fri_instance.rs`'s output — the FRI half of
 *  dregg's committed root proof, canonical. */
/** ⚑ ONE MMCS DIGEST LANE, AS THE EMITTER WRITES IT OR AS A RE-HASH WRITES IT.
 *  `number` is the emitter's spelling of a BabyBear lane; `string` is a decimal
 *  Pasta element, which does not fit a JS `number` and therefore cannot be
 *  smuggled in as one. Every consumer already goes through `BigInt(...)`, which
 *  takes either. See `RootConsume.rehashRealRootFri`. */
export type DigestLane = number | string;

export type RealRootFri = {
  kind: string;
  vkFingerprint: string;
  degreeBits: number[];
  knobs: FriKnobs;
  challengerStateBeforeFriAlpha: { width: number; rate: number; sponge: number[]; inputBuffer: number[]; outputBuffer: number[] };
  zeta: number[];
  airAlpha: number[];
  friAlpha: number[];
  betas: number[][];
  commits: DigestLane[][];
  finalPoly: number[][];
  queryPowWitness: number;
  inputRounds: {
    round: number;
    kindName: string;
    commit: DigestLane[];
    matrices: {
      matrix: number;
      instance: number;
      table: string;
      kindName: string;
      chunk: number | null;
      logHeight: number;
      width: number;
      points: number[][];
    }[];
  }[];
  openedEvals: {
    round: number;
    matrix: number;
    instance: number;
    table: string;
    kindName: string;
    chunk: number | null;
    logHeight: number;
    pointIndex: number;
    point: number[];
    values: number[][];
  }[];
  queries: {
    index: number;
    inputBatches: { matrices: { logHeight: number; width: number }[]; rows: number[][]; path: DigestLane[][] }[];
    reducedOpenings: { logHeight: number; ro: number[] }[];
    commitPhase: { sibling: number[]; path: DigestLane[][] }[];
    rollIns: { afterRound: number; value: number[] }[];
    foldedAfterRound: number[][];
  }[];
};

/**
 * The root's PCS round structure, READ OFF THE PROOF.
 *
 * ⚑ THE OPENING-POINT COUNT IS NOT 2, AND ASSUMING IT IS COSTS 168 PHANTOM
 * TERMS PER QUERY. `Const`, `Public`, `recompose` and `expose_claim` reference
 * no next-row main or preprocessed value, so their main and preprocessed
 * matrices are opened at ζ ALONE — one point, not two. Their PERMUTATION
 * matrices are opened at both, because a LogUp running sum always reads the
 * next row. A census that multiplies every width by two gets 2,798; the proof
 * says 2,630, and the shape is therefore taken from `inputRounds` rather than
 * derived from a table of widths.
 *
 * ⚑ AND THE ROUND ORDER IS THE PROOF'S. `main`, `quotient_chunk`,
 * `preprocessed`, `permutation` — not the order a reader would guess. It
 * matters twice: `alpha_pow` in `open_input` advances in ENCOUNTER order across
 * rounds, and each round's input commitment is indexed by it.
 *
 * ⚑ THE QUOTIENT CHUNKS SIT AT THE TRACE HEIGHT. `TwoAdicFriPcs` commits the
 * quotient over `create_disjoint_domain(1 << (db + log_quotient_degree))` split
 * into `n_chunks` pieces of `2^db` each, so a chunk's committed LDE height is
 * `db + log_blowup` — the same height as the instance's main matrix, which is
 * why no new height appears in the roll-in schedule.
 */
export function rootFriShape(real: RealRootFri): FriShape {
  //  ⚑ THE DUMPER EMITS THE KNOBS p3 READS, NOT THE DERIVED ONES, AND A MISSING
  //  DERIVED KNOB IS SILENT. `indexBits` and `extraQueryIndexBits` are this
  //  side's names for `log_global_max_height + extra`; left undefined they make
  //  `Array.from({length: undefined})` an EMPTY array, every path direction
  //  `undefined`, and every `undefined ? a : b` take the same branch — a walk
  //  that runs, proves, and is about nothing. It is completed here and asserted,
  //  rather than read optimistically at each use.
  const knobs: FriKnobs = {
    ...DEPLOYED_KNOBS,
    ...real.knobs,
    extraQueryIndexBits: real.knobs.extraQueryIndexBits ?? 0,
    indexBits:
      real.knobs.indexBits ?? real.knobs.logGlobalMaxHeight + (real.knobs.extraQueryIndexBits ?? 0),
  };
  for (const [k, v] of Object.entries(knobs))
    if (typeof v !== 'number' || !Number.isFinite(v))
      throw new Error(`FRI knob \`${k}\` is ${v} — the dumped knobs are incomplete`);
  const rounds: RoundSpec[] = real.inputRounds.map((r) => ({
    name: r.kindName as RoundSpec['name'],
    matrices: r.matrices.map((m) => ({
      instance: m.instance,
      name: m.chunk === null ? m.table : `${m.table}/chunk${m.chunk}`,
      logHeight: m.logHeight,
      width: m.width,
      numPoints: m.points.length,
    })),
  }));
  const heights = [...new Set(rounds.flatMap((r) => r.matrices.map((m) => m.logHeight)))].sort(
    (a, b) => b - a,
  );
  const lgmh = heights[0];
  if (lgmh !== knobs.logGlobalMaxHeight)
    throw new Error(
      `the tallest committed matrix is at 2^${lgmh} and the knobs say the global max height is ` +
        `2^${knobs.logGlobalMaxHeight} — one of them is describing a different proof`,
    );
  return { knobs, rounds, heights };
}

/** `(matrix, point, column)` triples in ONE query's `open_input`, by round. */
export function deepTermCensus(shape: FriShape): Record<string, number> & { total: number } {
  const out: any = { total: 0 };
  for (const r of shape.rounds) {
    const n = r.matrices.reduce((a, m) => a + m.width * m.numPoints, 0);
    out[r.name] = n;
    out.total += n;
  }
  return out;
}

// ===========================================================================
// 3. The two lane tables — what a slice may READ, and under which commitment.
// ===========================================================================

/**
 * The AIR chain's column assignment, as a lane index space. This is EXACTLY
 * `colChunks([...base, ...ext])`'s input order: every table's base columns in
 * legend order, then every table's extension columns, four lanes each.
 *
 * A `(round, matrix, point, column)` triple resolves to a lane here when the
 * AIR legend names it, and to the FRI-side table otherwise.
 */
export type AirColumnIndex = {
  /** `label -> global extension-value index` over the concatenated assignment. */
  byLabel: Map<string, number>;
  nBase: number;
  nExt: number;
  /** Per table, the base and ext offsets its legend indices are relative to. */
  tables: { name: string; baseOff: number; extOff: number }[];
};

export function airColumnIndex(): AirColumnIndex {
  const d = rootAirDag();
  const byLabel = new Map<string, number>();
  const tables: AirColumnIndex['tables'] = [];
  let baseOff = 0;
  for (const t of d.tables) {
    tables.push({ name: t.name, baseOff, extOff: 0 });
    t.cols.forEach((l, j) => byLabel.set(`${t.name}|${l}`, baseOff + j));
    baseOff += t.cols.length;
  }
  const nBase = baseOff;
  let extOff = 0;
  d.tables.forEach((t, ti) => {
    tables[ti].extOff = extOff;
    t.extCols.forEach((l, j) => byLabel.set(`${t.name}|${l}`, nBase + extOff + j));
    extOff += t.extCols.length;
  });
  return { byLabel, nBase, nExt: extOff, tables };
}

/** The AIR table names, keyed the way `root-air-dag.json` spells them, from the
 *  instance name the root proof carries. */
export const dagTableName = (instanceName: string): string =>
  instanceName.replace('poseidon2_perm/baby_bear_d4_', 'poseidon2_');

/**
 * Where one opened value lives.
 *
 *   * `air` — the AIR chain's assignment holds this exact number, at extension
 *     index `at`. The DEEP quotient reads it from there, and re-deriving
 *     `dagDigest` is what forces the two halves to agree.
 *   * `fri` — the AIR never reads it; it lives in the FRI-side lane table at
 *     extension index `at`, under `friDigest`.
 */
export type OpenedRef = { where: 'air' | 'fri'; at: number };

export type OpenedPlan = {
  /** `refs[round][matrix][point][column]`. */
  refs: OpenedRef[][][][];
  /** How many extension values the FRI-side table holds. */
  nFri: number;
  /** Census. */
  split: { air: number; fri: number; total: number };
};

/**
 * **THE FRI-SIDE LANE TABLE.** Everything the walk reads that the AIR chain's
 * assignment does not already hold, in one lane space with one digest over it.
 *
 * ⚑ WHY THE OPENED ROWS ARE IN HERE AND NOT WITNESSED FREELY. A Merkle sibling
 * can be witnessed by whichever slice needs it — bend it and the root check
 * fails, so it is self-authenticating. An opened ROW is not, because it is read
 * TWICE and by two different slices: the `inBlock` segments sponge it into a
 * leaf that the path binds to the commitment, and a `deep` segment thirty
 * slices later uses the same numbers as `f(x)`. Witnessed separately those are
 * two unrelated arrays, and the DEEP quotient would be over a row nothing
 * authenticated — a splice that every Merkle check in the walk still passes.
 * One commitment over the rows is what makes the two reads the same read.
 *
 * ⚑ AND THE PATHS ARE DELIBERATELY *NOT* IN HERE. 47,424 lanes of path digests
 * and siblings per proof, each read exactly once, each already pinned by the
 * opening it feeds. Committing to them would be 47,424 lanes of range checks
 * bought for nothing.
 */
export type FriLaneTable = {
  nLanes: number;
  /** The `DuplexChallenger` state the FRI transcript is entered at — a
   *  STAND-IN for a full `BatchTranscript` replay, and the walk's largest
   *  remaining soundness residual. It is committed here so both halves of the
   *  chain read the same one. */
  chalState: number;
  commit: number[];
  inputCommit: number[];
  finalPoly: number[];
  powWitness: number;
  /** `z[round][matrix][point]` — the out-of-domain point, 4 lanes. Per MATRIX,
   *  because `g·ζ` is taken in the matrix's OWN trace domain and the seven
   *  instances have five different ones. */
  z: number[][][];
  /** `fx[query][round][matrix]` — the lane the matrix's opened row starts at,
   *  in the SPONGE order `verify_batch` hashes: by round, then by height
   *  descending, then by matrix in round order. */
  fx: number[][][];
  /** The lane range one sponge block covers. */
  blockLanes: (q: number, round: number, height: number, block: number) => [number, number];
  perQueryRowLanes: number;
  /**
   * ⚑ THE PER-LANE KIND. `1` = a NATIVE field element (a Pasta MMCS digest, or a
   * Pasta challenger cell); `0` = a BabyBear lane, canonical below `2^31 − 1`.
   *
   * The table used to be homogeneous and `chunkedCommitment` put
   * `canonicalLane(l, 2^31 − 1)` on every lane it committed. Under the deployed
   * hash that is right end to end. Under Pasta the four round commitments, the
   * sixteen commit-phase commitments and the challenger state are 255-bit native
   * elements sharing a lane space with 31-bit opened values, and canonicalising
   * one refuses every honest proof. So the kind travels with the table and the
   * range check is a function of it.
   *
   * ⚠ THE OPENED VALUES, THE OPENING POINTS, THE FINAL POLYNOMIAL, THE PoW
   * WITNESS AND THE CARRIED CHALLENGES STAY BABYBEAR AT BOTH HASHES, and that is
   * not an oversight: `DreggMinaConfig` changes the HASH field only —
   * `Val = BabyBear`, `Challenge = EF4` — so everything the hash does not produce
   * is a BabyBear lane in both columns.
   */
  kinds: Uint8Array;
  /**
   * ⚑ THE CARRIED CHALLENGES, PRESENT EXACTLY WHEN THE WALK DOES NOT DERIVE
   * THEM (`WalkHash.transcript === 'carried'`), and `null` otherwise so the
   * deployed table's lane numbering is byte-identical to what it was.
   */
  carried: {
    /** FRI's batch-combination α — 4 lanes. */
    friAlpha: number;
    /** One fold challenge per commit-phase layer — 4 lanes each. */
    betas: number[];
    /** One canonical query index per query — 1 lane each. */
    qidx: number[];
  } | null;
};

export function friLaneTable(
  shape: FriShape,
  op: OpenedPlan,
  /** ⚑ THE WALK'S HASH, because BOTH the commitment widths and `blockLanes`
   *  are functions of it. A commitment is `digestLanes` lanes — eight under the
   *  deployed sponge, ONE under Pasta — and `blockLanes` has to agree with the
   *  block subdivision `segmentWalk` emitted at the same `spongeRate`. Passing
   *  the two independently is how a lane table and a segment list drift, so
   *  they come from one record. Defaulted so every deployed caller is
   *  unchanged. */
  hash: WalkHash = BABYBEAR_WALK_HASH,
): FriLaneTable {
  const spongeRate = hash.spongeRate;
  const carriedChal = hash.transcript === 'carried';
  let at = 0;
  const kindOf: number[] = [];
  const take = (n: number, kind = 0) => {
    const o = at;
    at += n;
    for (let i = 0; i < n; i++) kindOf.push(kind);
    return o;
  };
  //  ⚑ A DIGEST LANE'S KIND IS THE HASH'S, and it is the only thing in this
  //  table that is not a BabyBear lane. See `FriLaneTable.kinds`.
  const DK = hash.digestKind === 'native-field' ? 1 : 0;
  //  ⚑ A CARRIED WALK ALLOCATES NO ENTERING CHALLENGER STATE, because it enters
  //  no challenger. Committing to a state nothing reads would be a lane of
  //  witness the chain pays for and never uses.
  const chalState = carriedChal ? take(0, DK) : take(hash.chalStateLanes, DK);
  const commit = Array.from({ length: shape.knobs.layers }, () => take(hash.digestLanes, DK));
  const inputCommit = shape.rounds.map(() => take(hash.digestLanes, DK));
  const finalPoly = Array.from({ length: shape.knobs.finalPolyLen }, () => take(EXT_LANES));
  const powWitness = take(1);
  //  ⚑ THE CARRIED CHALLENGES SIT IN THE GLOBAL REGION, before the per-query
  //  rows — `uniformLayout` defines the global region as everything ahead of the
  //  19 opened-row blocks, and a challenge read by every query's block must be
  //  in it. They are BabyBear lanes at both hashes: `DreggMinaConfig` changes
  //  the hash field, not `Challenge = EF4`.
  const carried = carriedChal
    ? {
        friAlpha: take(EXT_LANES),
        betas: Array.from({ length: shape.knobs.layers }, () => take(EXT_LANES)),
        qidx: Array.from({ length: shape.knobs.numQueries }, () => take(1)),
      }
    : null;
  const z = shape.rounds.map((r) => r.matrices.map((m) => Array.from({ length: m.numPoints }, () => take(EXT_LANES))));
  //  The AIR-uncovered f(z): `planOpenedValues` already numbered them, and the
  //  numbering is dense, so one contiguous block holds them all.
  const fzBase = take(op.nFri * EXT_LANES);
  //  Re-point the fri refs at absolute lanes.
  for (const byMat of op.refs)
    for (const byPt of byMat)
      for (const byCol of byPt)
        for (const r of byCol) if (r.where === 'fri') r.at = fzBase + r.at * EXT_LANES;

  //  The opened rows, per query, in `verify_batch`'s hashing order.
  const roundOrder = shape.rounds.map((round) => {
    const hs = roundHeights(round);
    const order: number[] = [];
    for (const h of hs) round.matrices.forEach((m, mi) => m.logHeight === h && order.push(mi));
    return order;
  });
  const perQueryRowLanes = shape.rounds.reduce(
    (a, r) => a + r.matrices.reduce((b, m) => b + m.width, 0),
    0,
  );
  const fx: number[][][] = [];
  for (let q = 0; q < shape.knobs.numQueries; q++) {
    const byRound: number[][] = [];
    shape.rounds.forEach((round, ri) => {
      const perMat: number[] = new Array(round.matrices.length).fill(-1);
      for (const mi of roundOrder[ri]) perMat[mi] = take(round.matrices[mi].width);
      byRound.push(perMat);
    });
    fx.push(byRound);
  }

  const blockLanes = (q: number, ri: number, height: number, block: number): [number, number] => {
    const round = shape.rounds[ri];
    const mats = roundOrder[ri].filter((mi) => round.matrices[mi].logHeight === height);
    const start = fx[q][ri][mats[0]];
    const w = mats.reduce((a, mi) => a + round.matrices[mi].width, 0);
    const a = start + block * spongeRate;
    return [a, Math.min(a + spongeRate, start + w)];
  };

  return {
    nLanes: at,
    chalState,
    commit,
    inputCommit,
    finalPoly,
    powWitness,
    z,
    fx,
    blockLanes,
    perQueryRowLanes,
    kinds: Uint8Array.from(kindOf),
    carried,
  };
}

/** ⚑ THE LANE KIND OF A LANE THE UNIFORM TABLE HAS RE-ADDRESSED. `kinds` is
 *  indexed by the DEPLOYED numbering; `uniformLaneTable` moves each query's rows
 *  onto a chunk boundary and pads with zeros, so a uniform table's kind vector
 *  is rebuilt at its own length. Padding lanes are BabyBear-kind, which is what
 *  makes canonicalising them (they are zero) correct. */
export function remapKinds(kinds: Uint8Array, nLanes: number, remap: (l: number) => number): Uint8Array {
  const out = new Uint8Array(nLanes);
  for (let l = 0; l < kinds.length; l++) {
    const to = remap(l);
    if (to >= 0 && to < nLanes) out[to] = kinds[l];
  }
  return out;
}

/**
 * Resolve every opened value against the AIR legend.
 *
 * The legend labels are the contract: `main[0][i]` is main column `i` at ζ,
 * `main[1][i]` the same column at `g·ζ`, `prep[a][j]` likewise, and
 * `perm[a][k]` the `k`-th extension permutation column. An extension
 * permutation column occupies FOUR base lanes in the PCS commitment and ONE
 * extension value in the AIR assignment, so the four consecutive PCS columns
 * `4k .. 4k+3` resolve to the four lanes of AIR extension value `perm[a][k]`.
 */
export function planOpenedValues(shape: FriShape, air: AirColumnIndex): OpenedPlan {
  const refs: OpenedRef[][][][] = [];
  let nFri = 0;
  let nAir = 0;
  for (const r of shape.rounds) {
    const byMat: OpenedRef[][][] = [];
    for (const m of r.matrices) {
      const t = dagTableName(m.name.split('/chunk')[0]);
      const byPt: OpenedRef[][] = [];
      for (let p = 0; p < m.numPoints; p++) {
        const byCol: OpenedRef[] = [];
        for (let c = 0; c < m.width; c++) {
          let label: string | null = null;
          //  ⚑ THE PERMUTATION ROUND IS NOT DIRECTLY IN THE AIR'S ASSIGNMENT,
          //  AND ASSUMING IT WAS IS A REAL ERROR THIS LEG MADE AND MEASURED.
          //  The PCS commits an extension permutation column as FOUR BASE
          //  columns and opens each of them at ζ, giving four EXTENSION values
          //  `f_j(ζ)`. The AIR holds ONE extension value, the whole column's
          //  opening. They are related — `perm[p][k] = Σ_j f_{4k+j}(ζ)·X^j` —
          //  and they are not equal, so the four components go under
          //  `friDigest` and `permBind` asserts the recomposition. That check is
          //  query-INDEPENDENT and is therefore paid ONCE for the whole walk,
          //  not once per query.
          if (r.name === 'main') label = `main[${p}][${c}]`;
          else if (r.name === 'preprocessed') label = `prep[${p}][${c}]`;
          //  `permutation` and `quotient_chunk` are never in the AIR's assignment.
          // The quotient chunks are never in the AIR's assignment.
          const key = label === null ? null : `${t}|${label}`;
          const hit = key === null ? undefined : air.byLabel.get(key);
          if (hit === undefined) {
            byCol.push({ where: 'fri', at: nFri++ });
          } else {
            byCol.push({ where: 'air', at: hit });
            nAir++;
          }
        }
        byPt.push(byCol);
      }
      byMat.push(byPt);
    }
    refs.push(byMat);
  }
  return { refs, nFri, split: { air: nAir, fri: nFri, total: nAir + nFri } };
}

// ===========================================================================
// 4. Slots — the state that crosses a cut.
// ===========================================================================

/**
 * Every value that can be live at a slice boundary, as a flat lane space.
 *
 * ⚑ ONE SLOT SET FOR ALL 19 QUERIES, and that is not an approximation. A
 * query's running Merkle digest, sponge state and fold value are dead the
 * moment its walk ends, so re-using the same slot ids is what LIVENESS is for:
 * the backward pass below kills a slot at the segment that overwrites it, and a
 * boundary inside query 7 carries query 7's fold value and nothing of query 6's.
 */
export type SlotLayout = {
  n: number;
  chal: number[];
  alpha: number[];
  beta: number[][];
  qidx: number[];
  cur: number[];
  sponge: number[];
  /** One pending mixed-height digest per height BELOW the round's tallest. A
   *  round's shorter matrices are sponged when their rows are read and sit here
   *  until the Merkle walk reaches the level their height names — up to four of
   *  them live at once, which is why this is not one slot. */
  inj: number[][];
  dacc: number[][];
  dpow: number[][];
  ro: number[][];
  /** The running Horner accumulator of ONE (matrix, point), which is live only
   *  when that matrix's columns are split across a cut. */
  dh: number[];
  folded: number[];
  x: number;
  /** ⚑ APPENDED AFTER `x`, DELIBERATELY. The preamble's three outputs are new
   *  slots and every existing slot keeps its id, so a plan built without a
   *  preamble is byte-identical to the one the braid measured. */
  permChal: number[][];
  airAlpha: number[];
  zetaS: number[];
  names: string[];
  /**
   * ⚑ PER-SLOT KIND, for `FriLaneTable.kinds`' reason one level up. A slice
   * CANONICALISES every carried slot on the way in — which is right for a
   * BabyBear lane and refuses every honest Pasta digest, and the slots that hold
   * digests (`cur`, the mixed-height `inj` registers) and the leaf sponge's
   * running state are exactly the ones whose kind is the hash's.
   */
  kinds: Uint8Array;
};

export function slotLayout(
  shape: FriShape,
  nPermChal = 0,
  hash: WalkHash = BABYBEAR_WALK_HASH,
): SlotLayout {
  const names: string[] = [];
  const kinds: number[] = [];
  const take = (label: string, n: number, kind = 0): number[] => {
    const out: number[] = [];
    for (let i = 0; i < n; i++) {
      out.push(names.length);
      names.push(`${label}[${i}]`);
      kinds.push(kind);
    }
    return out;
  };
  const DK = hash.digestKind === 'native-field' ? 1 : 0;
  //  ⚑ A CARRIED WALK HOLDS NO CHALLENGER STATE — see `friLaneTable`.
  const chal = take('chal', hash.transcript === 'carried' ? 0 : hash.chalStateLanes, DK);
  const alpha = take('alpha', EXT_LANES);
  const beta = Array.from({ length: shape.knobs.layers }, (_, r) => take(`beta${r}`, EXT_LANES));
  const qidx = take('qidx', shape.knobs.numQueries);
  const cur = take('cur', hash.digestLanes, DK);
  //  ⚑ THE LEAF SPONGE'S RUNNING STATE IS THE HASH'S OWN FIELD: sixteen
  //  BabyBear lanes, or three Pasta cells.
  const sponge = take('sponge', hash.spongeStateLanes, DK);
  const inj = shape.heights.map((h) => take(`inj${h}`, hash.digestLanes, DK));
  const dacc = shape.heights.map((h) => take(`dacc${h}`, EXT_LANES));
  const dpow = shape.heights.map((h) => take(`dpow${h}`, EXT_LANES));
  const ro = shape.heights.map((h) => take(`ro${h}`, EXT_LANES));
  const dh = take('dh', EXT_LANES);
  const folded = take('folded', EXT_LANES);
  const x = take('x', 1)[0];
  const permChal = Array.from({ length: nPermChal }, (_, i) => take(`permChal${i}`, EXT_LANES));
  const airAlpha = nPermChal > 0 ? take('airAlpha', EXT_LANES) : [];
  const zetaS = nPermChal > 0 ? take('zeta', EXT_LANES) : [];
  return {
    n: names.length,
    chal,
    alpha,
    beta,
    qidx,
    cur,
    sponge,
    inj,
    dacc,
    dpow,
    ro,
    dh,
    folded,
    x,
    permChal,
    airAlpha,
    zetaS,
    names,
    kinds: Uint8Array.from(kinds),
  };
}

// ===========================================================================
// 5. The segments.
// ===========================================================================

/** A lane of the FRI transcript's absorb schedule. */
export type AbsorbRef =
  | { src: 'commit'; layer: number; lane: number }
  | { src: 'finalPoly'; i: number; lane: number }
  | { src: 'arity' } //  a COMPILE-TIME constant, not proof data
  | { src: 'pow' }
  // ---- the batch-STARK preamble (`preambleOps`) -----------------------------
  /** A protocol SHAPE constant — the instance count, a degree-bits field, an
   *  AIR width, a quotient-chunk count, a preprocessed width, or one of the
   *  three zero limbs `observe_usize` lifts a `usize` into. The circuit absorbs
   *  a LITERAL, so this is the part of the transcript a prover cannot reach at
   *  all. */
  | { src: 'shape'; v: number; what: string }
  /** One lane of one of the four PCS round commitments — the SAME `inputCommit`
   *  lanes the walk's `inRoot` segments close their Merkle roots against. */
  | { src: 'roundCommit'; round: number; lane: number }
  /** One public value, at AIR extension index `at` — a BASE element, so lane
   *  `4·at` alone, not four. */
  | { src: 'publicValue'; at: number }
  /** One lane of one global-lookup cumulative sum, at AIR extension index `at`.
   *  The AIR chain reads the same value as `perm_value[i]`. */
  | { src: 'cumSum'; at: number; lane: number }
  /** One lane of one opened value, resolved through `OpenedPlan` exactly as the
   *  DEEP quotient resolves it — 47% of them literally the AIR chain's own
   *  lanes, under `dagDigest`. */
  | { src: 'opened'; round: number; mat: number; point: number; col: number; lane: number };

export type SampleRef =
  | { dst: 'alpha'; lane: number }
  | { dst: 'beta'; layer: number; lane: number }
  /** The `query_pow_bits = 16` grind's own sample. It lands in no slot — the
   *  circuit asserts its low 16 bits are zero and drops it — but it CONSUMES an
   *  output-buffer position, and a schedule that skipped it would draw all 19
   *  query indices one position early. */
  | { dst: 'pow' }
  | { dst: 'qidx'; query: number }
  // ---- the batch-STARK preamble --------------------------------------------
  /** A LogUp permutation challenge. The AIR chain reads these as `challenge[k]`
   *  and today witnesses them; derived here, they stop being the prover's. */
  | { dst: 'permChal'; i: number; lane: number }
  /** The AIR's constraint-folding α — NOT FRI's batch-combination α. */
  | { dst: 'airAlpha'; lane: number }
  | { dst: 'zeta'; lane: number };

/** Where a `duplex` segment's ENTERING sponge state comes from.
 *
 *  ⚑ THIS WAS `k === 0` AND IT IS NOW EXPLICIT, because the preamble makes the
 *  walk's first segment a different object. `chalState` is the witnessed
 *  entering state (§3.14 residual 1, the shape this module exists to remove);
 *  `zero` is `DuplexChallenger::new`'s all-zero sponge, a compile-time literal. */
export type DuplexEntry = 'chalState' | 'zero' | 'carry';

export type Segment =
  /** One challenger permutation, with the lanes it absorbed and the challenges
   *  drawn from its output buffer before the next one. */
  | {
      t: 'duplex';
      absorbs: AbsorbRef[];
      samples: SampleRef[];
      perm: boolean;
      rows: number;
      entry: DuplexEntry;
    }
  /**
   * ⚑ THE CARRIED TRANSCRIPT, AS ONE SEGMENT — what a `transcript: 'carried'`
   * walk emits INSTEAD of the duplex run, not in addition to it.
   *
   * It reads FRI's α, the sixteen βs and the nineteen query indices out of the
   * committed lane table into their slots. Every one of them is therefore under
   * `friDigest` and under the chain's boundary — a prover cannot vary them
   * between two slices, and the whole walk downstream is over ONE set of
   * challenges. What it does NOT establish is that they are the challenges the
   * batch-STARK's own transcript would have produced: that is `preSeal`'s job
   * and it exists only for the hash whose challenger is modelled. §3.14
   * residual 1, said in a segment rather than a footnote.
   *
   * ⚑ THE QUERY INDEX IS RANGE-CHECKED HERE AND THE CHECK IS THE POINT. The
   * derived path carries a recomposition of `indexBits` forced bits; this one
   * carries a committed lane, so the segment witnesses the bits, recomposes, and
   * asserts equality — the same bound, imposed at the read instead of at the
   * draw.
   */
  | { t: 'chalCarry'; rows: number }
  /** One `PaddingFreeSponge` block over the concatenated opened rows at one
   *  height of one input round. `first` starts the sponge, `last` finishes it
   *  into a digest. */
  | {
      t: 'inBlock';
      q: number;
      round: number;
      height: number;
      block: number;
      lanes: number;
      first: boolean;
      last: boolean;
      /** TRUE when this digest is the round's TALLEST — it seeds `cur`;
       *  otherwise it is compressed in as a mixed-height injection. */
      seeds: boolean;
      rows: number;
    }
  /** One Merkle level of an input-round opening, plus the injection that
   *  follows it when a shorter matrix's height is reached here. */
  | { t: 'inLevel'; q: number; round: number; level: number; inject: number | null; rows: number }
  /** `cur == commitment` for an input round. */
  | { t: 'inRoot'; q: number; round: number; rows: number }
  /** A DEEP-quotient term run: columns `[from, to)` of one (matrix, point).
   *  `open` computes `1/(z − x)` and `close` folds the result into the height's
   *  accumulator and advances `alpha_pow`. */
  | {
      t: 'deep';
      q: number;
      round: number;
      mat: number;
      point: number;
      from: number;
      to: number;
      open: boolean;
      close: boolean;
      rows: number;
    }
  /** The commit-phase row: reconstruct `[even, odd]` from the running fold value
   *  and the witnessed sibling, hash the leaf, fold at β, descend the coset
   *  point. One segment, for the reason the emitter gives. */
  | { t: 'cpLeaf'; q: number; r: number; rows: number }
  | { t: 'cpLevel'; q: number; r: number; level: number; rows: number }
  | { t: 'cpRoot'; q: number; r: number; rows: number }
  /** The reduced opening scheduled to roll in after this round's fold. Emitted
   *  only for the four rounds that have one. */
  | { t: 'cpFold'; q: number; r: number; rollIn: number; rows: number }
  /** Seed one query's DEEP accumulators: `acc = 0` and `alpha_pow = 1` per
   *  HEIGHT. ⚑ Free in rows and not optional — `alpha_pow` starting at zero
   *  makes every reduced opening zero, and a chain of zeros folds and closes
   *  against a final polynomial of zero without complaining. */
  | { t: 'deepInit'; q: number; rows: number }
  /** ⚑ THE PERMUTATION ROUND'S BRIDGE TO THE AIR HALF, paid ONCE for the whole
   *  walk: extension permutation columns `[from, to)` of one (matrix, point) of
   *  the permutation round, each asserted to be `Σ_j f_{4k+j}(ζ)·X^j` over the
   *  four base components the PCS opened. Without it those 512 opened values
   *  are authenticated by the FRI walk and connected to nothing the AIR read. */
  | { t: 'permBind'; mat: number; point: number; from: number; to: number; rows: number }
  /** The chain lands on the final polynomial. */
  | { t: 'final'; q: number; rows: number }
  /** ⚑ THE PREAMBLE'S CLOSING EQUALITY, and the reason a forged preamble is
   *  refused HERE rather than twelve slices later at a Merkle root.
   *
   *  The preamble does not merely reach a state — it re-derives two things both
   *  halves of the braid already use: `ζ`, the out-of-domain point every matrix
   *  is opened at, and the LogUp challenges the AIR chain folds its permutation
   *  constraints with. Asserting the derivation reproduces them is what makes
   *  the transcript's inputs load-bearing: bend ANY absorbed value — a public
   *  value, a cumulative sum, a commitment lane, one of the 2,630 opened values
   *  — and `ζ` moves, and this segment refuses.
   *
   *  Without it a bent input would produce a perfectly self-consistent wrong
   *  transcript whose first contradiction is a Merkle root ~12 slices in. */
  | {
      t: 'preSeal';
      /** FRI lanes of every matrix's point-0 opening point. */
      zetaAt: number[];
      /** `{ at }` an AIR extension index holding a `challenge[k]` the AIR chain
       *  reads, `{ chal }` the sampled challenge it must equal. */
      chalAt: { at: number; chal: number }[];
      /** ⚑ FALSE builds the UNSEALED CONTROL: identical segments, identical
       *  lane reads, identical rows — only the closing equalities removed. That
       *  is what makes a refusal attributable to the seal rather than to the
       *  forged proof being malformed somewhere else. */
      armed: boolean;
      rows: number;
    };

// ===========================================================================
// 4b. THE BATCH-STARK PREAMBLE — what the challenger state entering FRI is a
//     function of, read off p3's own source rather than reconstructed.
// ===========================================================================

/**
 * The shape of the batch-STARK the preamble transcribes. Everything here is a
 * COMPILE-TIME fact about the root's seven instances; the values the script
 * absorbs are proof data and live in the two lane tables.
 */
export type PreambleMeta = {
  instances: {
    /** The `root-air-dag.json` spelling, for the AIR-lane lookups. */
    name: string;
    degreeBits: number;
    width: number;
    nChunks: number;
    prepWidth: number;
    /** AIR extension indices of this instance's public values, in order. */
    publicAt: number[];
    /** AIR extension indices of this instance's global-lookup cumulative sums,
     *  in `global_lookup_data[i]` order. */
    cumSumAt: number[];
  }[];
  /** `lookupBuses[i][j]` — the bus name of instance `i`'s `j`-th lookup context,
   *  or `null` for a `Kind::Local` one. ⚑ p3 samples a Global bus's challenges
   *  ONCE, on first encounter, and every later context with that name reuses
   *  them; a Local one samples fresh. Getting this wrong changes the number of
   *  permutations, not just the values. */
  lookupBuses: (string | null)[][];
  /** `LogUpGadget::num_challenges()` — 2. */
  challengesPerLookup: number;
};

export type PreOp = { t: 'observe'; a: AbsorbRef } | { t: 'sample'; s: SampleRef };

/** The shape of `root_air_instance.rs`'s output that the preamble needs. Kept
 *  structural rather than importing `RealRootAir`, so this module does not gain
 *  a dependency on the AIR emitter's whole record. */
export type PreambleSource = {
  instances: {
    table: string;
    degreeBits: number;
    width: number;
    prepWidth: number;
    nChunks: number;
    publicValues: number[];
    permutationValues: number[][];
    lookups: { kind: string; bus: string }[];
  }[];
};

/**
 * Build the preamble's compile-time shape from the root proof, resolving every
 * proof-data input to a lane of the AIR chain's OWN committed assignment.
 *
 * ⚑ EVERY VALUE THE PREAMBLE ABSORBS THAT IS NOT A LITERAL IS ALREADY UNDER A
 * COMMITMENT THE BRAID CARRIES. The public values are `expose_claim|public[i]`
 * and the cumulative sums are `<table>|perm_value[i]` — both `dagDigest` lanes,
 * both read by the AIR half; the four round commitments are `ft.inputCommit`,
 * the lanes the walk's own Merkle roots close against; the 2,630 opened values
 * resolve through the same `OpenedPlan` the DEEP quotient uses. There is no
 * fresh witness anywhere in the derivation, which is the property that makes it
 * a derivation.
 */
export function rootPreambleMeta(real: PreambleSource, air: AirColumnIndex): PreambleMeta {
  const at = (label: string): number => {
    const g = air.byLabel.get(label);
    if (g === undefined)
      throw new Error(
        `the AIR legend does not name \`${label}\` — the preamble would have to WITNESS a value ` +
          'the AIR chain does not commit, which is the hole it exists to close',
      );
    return g;
  };
  return {
    instances: real.instances.map((inst) => {
      const t = dagTableName(inst.table);
      return {
        name: t,
        degreeBits: inst.degreeBits,
        width: inst.width,
        nChunks: inst.nChunks,
        prepWidth: inst.prepWidth,
        publicAt: inst.publicValues.map((_, i) => at(`${t}|public[${i}]`)),
        cumSumAt: inst.permutationValues.map((_, i) => at(`${t}|perm_value[${i}]`)),
      };
    }),
    lookupBuses: real.instances.map((inst) =>
      inst.lookups.map((l) => (l.kind === 'global' ? l.bus : null)),
    ),
    //  `LogUpGadget::num_challenges()` — `lookup/src/logup.rs:269`.
    challengesPerLookup: 2,
  };
}

/**
 * **THE PREAMBLE SCRIPT.** `verify_batch`'s transcript from
 * `initialise_challenger()` to `verify_fri`'s door, as an ordered op list.
 *
 * Read off, line for line, and every line cited because the four defects the
 * FRI walk paid for were all ordering or convention errors that looked fine:
 *
 * | | source |
 * |---|---|
 * | `observe_instance_count(n)` | `batch-stark/src/verifier/mod.rs:144` |
 * | `observe_instance_binding(ext_db, base_db, width, n_chunks)` × n | `:274` |
 * | `observe_main(main_commit, public_values)` | `:278` |
 * | `observe_preprocessed(prep_widths, prep_commit)` | `:279` |
 * | `sample_perm_challenges` | `:289` |
 * | `observe_perm_and_sample_alpha(perm_commit, cumulative sums)` | `:290` |
 * | `observe_quotient_commitment` | `:294` |
 * | `sample_zeta` | `:300` |
 * | every claimed evaluation, in round / matrix / point order | `fri/src/two_adic_pcs.rs:782-788` |
 *
 * ⚑ THE COMMITMENT-OBSERVE ORDER IS NOT THE PCS ROUND ORDER. The transcript
 * absorbs **main, preprocessed, permutation, quotient**; `coms_to_verify` is
 * built **main, quotient, preprocessed, permutation**, and it is the second
 * order the opened values are absorbed in. Reading one for the other gives a
 * well-formed, completely different transcript — it is polarity 1 of the leg's
 * discriminating table.
 *
 * ⚑ `observe_usize(v)` IS FOUR ELEMENTS, NOT ONE. `observe_base_as_algebra_element::<EF>`
 * lifts to the extension and absorbs the basis coefficients — `[v, 0, 0, 0]`
 * (`challenger/src/lib.rs:141-147`). Absorbing one costs 14 fewer permutations
 * and every challenge after the first.
 */
export function preambleOps(
  shape: FriShape,
  meta: PreambleMeta,
  hash: WalkHash = BABYBEAR_WALK_HASH,
): PreOp[] {
  const ops: PreOp[] = [];
  const obs = (a: AbsorbRef) => ops.push({ t: 'observe', a });
  const smp = (s: SampleRef) => ops.push({ t: 'sample', s });
  /** `observe_base_as_algebra_element::<Challenge>(F::from_usize(v))`. */
  const usize = (v: number, what: string) => {
    obs({ src: 'shape', v, what });
    for (let j = 1; j < EXT_LANES; j++) obs({ src: 'shape', v: 0, what: `${what}#pad${j}` });
  };
  const roundIx = (name: RoundSpec['name']) => {
    const i = shape.rounds.findIndex((r) => r.name === name);
    if (i < 0) throw new Error(`the proof has no ${name} round — the preamble script cannot be built`);
    return i;
  };
  const commit = (name: RoundSpec['name']) => {
    const r = roundIx(name);
    for (let l = 0; l < hash.digestLanes; l++) obs({ src: 'roundCommit', round: r, lane: l });
  };

  const n = meta.instances.length;
  usize(n, 'instanceCount');
  for (let i = 0; i < n; i++) {
    const inst = meta.instances[i];
    //  `validate_degree_bits(.., is_zk = 0, ..)` returns `base_db == ext_db`.
    usize(inst.degreeBits, `inst${i}.logExtDegree`);
    usize(inst.degreeBits, `inst${i}.logDegree`);
    usize(inst.width, `inst${i}.width`);
    usize(inst.nChunks, `inst${i}.numQuotientChunks`);
  }
  commit('main');
  for (let i = 0; i < n; i++)
    for (const at of meta.instances[i].publicAt) obs({ src: 'publicValue', at });
  for (let i = 0; i < n; i++) usize(meta.instances[i].prepWidth, `inst${i}.prepWidth`);
  commit('preprocessed');

  //  `transcript.rs:74-102` — a Global bus samples once, on FIRST ENCOUNTER.
  {
    const { base } = permChalAssignment(meta);
    const drawn = new Set<number>();
    for (let i = 0; i < n; i++)
      for (const b of base[i] ?? []) {
        if (drawn.has(b)) continue;
        drawn.add(b);
        for (let c = 0; c < meta.challengesPerLookup; c++)
          for (let l = 0; l < EXT_LANES; l++) smp({ dst: 'permChal', i: b + c, lane: l });
      }
  }

  commit('permutation');
  for (let i = 0; i < n; i++)
    for (const at of meta.instances[i].cumSumAt)
      for (let l = 0; l < EXT_LANES; l++) obs({ src: 'cumSum', at, lane: l });
  for (let l = 0; l < EXT_LANES; l++) smp({ dst: 'airAlpha', lane: l });

  commit('quotient_chunk');
  for (let l = 0; l < EXT_LANES; l++) smp({ dst: 'zeta', lane: l });

  //  `two_adic_pcs.rs:782-788` — in `coms_to_verify` order, which is the round
  //  order the shape already carries.
  shape.rounds.forEach((round, ri) =>
    round.matrices.forEach((m, mi) => {
      for (let pt = 0; pt < m.numPoints; pt++)
        for (let c = 0; c < m.width; c++)
          for (let l = 0; l < EXT_LANES; l++)
            ops.push({ t: 'observe', a: { src: 'opened', round: ri, mat: mi, point: pt, col: c, lane: l } });
    }),
  );
  return ops;
}

/**
 * The FRI-lane index of each committed matrix's POINT-0 opening point — ζ, for
 * every matrix, because `verify_batch` opens all of them there.
 *
 * ⚑ TWO NUMBERINGS OF ONE TABLE IS THE SHAPE THAT DRIFTS, so this repeats
 * `friLaneTable`'s prefix arithmetic on purpose and `assertPreambleSealLanes`
 * requires the two to agree. `segmentWalk` cannot take an `ft` — the table is
 * built FROM the walk — so the choice is this or a lane number smuggled through
 * the meta.
 */
export function preambleZetaLanes(
  shape: FriShape,
  hash: WalkHash = BABYBEAR_WALK_HASH,
): number[] {
  let at =
    hash.chalStateLanes +
    shape.knobs.layers * hash.digestLanes +
    shape.rounds.length * hash.digestLanes +
    shape.knobs.finalPolyLen * EXT_LANES +
    1;
  const out: number[] = [];
  for (const r of shape.rounds)
    for (const m of r.matrices) {
      out.push(at); //  point 0 is ζ; point 1, where present, is `g·ζ`
      at += m.numPoints * EXT_LANES;
    }
  return out;
}

/** Require the two numberings to agree, lane for lane. */
export function assertPreambleSealLanes(
  shape: FriShape,
  ft: FriLaneTable,
  hash: WalkHash = BABYBEAR_WALK_HASH,
) {
  const mine = preambleZetaLanes(shape, hash);
  let i = 0;
  shape.rounds.forEach((r, ri) =>
    r.matrices.forEach((_, mi) => {
      if (mine[i] !== ft.z[ri][mi][0])
        throw new Error(
          `the preamble seal points at FRI lane ${mine[i]} for round ${ri} matrix ${mi} and the ` +
            `lane table says ${ft.z[ri][mi][0]} — two numberings of one table have drifted`,
        );
      i++;
    }),
  );
  if (i !== mine.length) throw new Error(`the preamble seal names ${mine.length} matrices, the shape has ${i}`);
}

/**
 * `base[i][j]` — the index of the FIRST sampled challenge that instance `i`'s
 * `j`-th lookup context uses, and `total`, how many are sampled.
 *
 * ⚑ THE SHARING IS NOT MODULAR AND ASSUMING IT IS WOULD BE RIGHT ON THIS PROOF
 * AND WRONG IN GENERAL. Every one of the root's 64 lookup contexts is on the
 * single `WitnessChecks` bus, so today `challenge[k] == permChal[k mod 2]` — a
 * coincidence of this batch, not the protocol. p3 keys the map by NAME
 * (`transcript.rs:84-99`): a second bus, or a `Kind::Local` context, samples a
 * fresh pair and the modular reading silently binds the wrong challenge. The
 * near-miss this repo already paid for — 216 of 512 permutation values matching
 * by coincidence — is the same shape.
 */
export function permChalAssignment(meta: PreambleMeta): { base: number[][]; total: number } {
  const seen = new Map<string, number>();
  const base: number[][] = [];
  let n = 0;
  for (const ctxs of meta.lookupBuses) {
    const row: number[] = [];
    for (const bus of ctxs ?? []) {
      if (bus !== null && seen.has(bus)) {
        row.push(seen.get(bus)!);
        continue;
      }
      if (bus !== null) seen.set(bus, n);
      row.push(n);
      n += meta.challengesPerLookup;
    }
    base.push(row);
  }
  return { base, total: n };
}

/** How many LogUp challenges `preambleOps` samples. */
export function preambleChallengeCount(meta: PreambleMeta): number {
  return permChalAssignment(meta).total;
}

export type SegmentedWalk = {
  shape: FriShape;
  /** `'shaped'` — the price and the shape are one hash. `'price-only'` — the
   *  shape is `hash` and the unit prices are another hash's, i.e. a PROJECTION.
   *  Carried so a report cannot lose the distinction between the two. */
  priced: 'shaped' | 'price-only';
  /** ⚑ THE WALK CARRIES ITS OWN HASH SHAPE. `segmentReads`, `auxLanes`,
   *  `runSegments` and the uniform planner all need the digest width and the
   *  sponge state width, and every one of them taking its own parameter is how
   *  a lane table and an executor come to disagree about how many lanes a
   *  Merkle sibling is. There is one answer and it travels with the walk. */
  hash: WalkHash;
  slots: SlotLayout;
  segs: Segment[];
  reads: number[][];
  writes: number[][];
  /** `liveIn[k]` — the slots that must cross the boundary BEFORE segment `k`. */
  liveIn: number[][];
  /** Total modelled rows. */
  totalRows: number;
};

const ceilDiv = (a: number, b: number) => Math.ceil(a / b);

/** The concatenated opened-row width at one height of one round. */
export function rowWidthAt(round: RoundSpec, height: number): number {
  return round.matrices.filter((m) => m.logHeight === height).reduce((a, m) => a + m.width, 0);
}

/** The heights present in a round, DESCENDING. */
export function roundHeights(round: RoundSpec): number[] {
  return [...new Set(round.matrices.map((m) => m.logHeight))].sort((a, b) => b - a);
}

/**
 * **THE SEGMENT LIST.** The whole walk, in the order a verifier runs it:
 * the FRI transcript, then per query the input-phase openings, the DEEP
 * quotient, and the fold chain onto the final polynomial.
 */
export function segmentWalk(
  shape: FriShape,
  opts: {
    deepCols?: number;
    preamble?: PreambleMeta;
    seal?: boolean;
    price?: WalkPrice;
    /** ⚑ THE WALK'S HASH — its SHAPE, not its price. See `WalkHash`. */
    hash?: WalkHash;
    /**
     * ⚑ NAME THE HYBRID OR BE REFUSED. Pricing a BabyBear-SHAPED walk at Pasta
     * unit prices is what `MINA-VERIFIES-DREGG-FRI-SIZE` §3.31 reports as
     * `2.906e6 rows = 54 slices`, and it is a legitimate PROJECTION: the
     * arithmetic terms are hash-independent and the hash terms are measured, so
     * the total is a real estimate of what the same statement costs at the other
     * hash. What it is NOT is a walk over a Pasta-hashed proof — its digests are
     * still eight lanes, its commitments still occupy eight lanes of the lane
     * table, and its transcript is still the duplex challenger. Passing a price
     * whose sponge rate disagrees with the shape without saying `priceOnly` is
     * refused, because that combination reads as a measurement and is not one.
     */
    priceOnly?: boolean;
  } = {},
): SegmentedWalk {
  const H = opts.hash ?? BABYBEAR_WALK_HASH;
  //  ⚑ THE REFUSAL, AND IT IS THE POINT OF `WalkHash.transcript`. Everything
  //  below the transcript — the leaf sponges, the Merkle levels, the DEEP
  //  quotient, the fold chain — is a substitution this record already carries.
  //  The transcript is a different state machine, `challengerRun` below
  //  implements exactly one of them, and there is no oracle for the other. A
  //  walk that emitted `duplex` segments under a hash whose challenger packs
  //  and splits would model a protocol nobody runs, and every downstream
  //  measurement would be a number about it.
  if (H.transcript === 'unimplemented')
    throw new Error(
      `\`segmentWalk\` has no transcript model for '${H.name}'. The Merkle half of this hash is ` +
        'threaded (digest width, sponge rate, slot layout, aux widths, the executor); the ' +
        'CHALLENGER is not. `MultiField32Challenger` packs eight BabyBear lanes into a Pasta ' +
        'cell to absorb, splits a cell into seven canonical limbs to squeeze, absorbs a digest ' +
        'NATIVELY after flushing the pending base buffer, tags the capacity with a length and ' +
        'pops its queue from the back — none of which `challengerRun` emits. And dregg mints no ' +
        'Pasta-hashed root, so a model written here would have nothing to be checked against. ' +
        'Price this walk with `priceForSuite` and measure the consumer with `root-consume-rows`; ' +
        'building the sliced chain at this hash needs the transcript first.',
    );
  //  ⚑ A CARRIED WALK CANNOT HAVE A PREAMBLE, and the refusal is by NAME. The
  //  preamble IS the derivation `carried` says is absent; emitting one at a hash
  //  whose challenger `challengerRun` does not model would produce a
  //  perfectly self-consistent transcript for a protocol nobody runs, which is
  //  the exact outcome `transcript: 'unimplemented'` exists to prevent.
  if (H.transcript === 'carried' && opts.preamble)
    throw new Error(
      `the walk shape '${H.name}' CARRIES its challenges (\`transcript: 'carried'\`) and was given a ` +
        'batch-STARK preamble to derive them with. The preamble runs `challengerRun`, which models ' +
        '`DuplexChallenger` alone; at this hash the transcript is a `MultiField32Challenger` and ' +
        'there is no object to check a model of it against. Drop the preamble and read the residual ' +
        'in `ROOT_CHALLENGE_STATUS`, or implement the challenger first.',
    );
  const hybrid = !!opts.price && opts.price.spongeRate !== H.spongeRate;
  if (hybrid && opts.priceOnly !== true)
    throw new Error(
      `the price table absorbs ${opts.price!.spongeRate} lanes a sponge permutation and the walk ` +
        `shape '${H.name}' absorbs ${H.spongeRate}. A walk priced at one hash and SHAPED like ` +
        'another is a PROJECTION, not a measurement — pass `priceOnly: true` to say so, or pass ' +
        'a `hash` that matches the price.',
    );
  //  ⚑ A PRICE-ONLY WALK KEEPS THE PRICE TABLE'S SPONGE RATE, because the block
  //  COUNT is the thing the other hash's rate actually changes and the whole
  //  point of the projection is to carry that. Everything structural — digest
  //  width, slot layout, lane table — stays this walk's shape, which is why the
  //  result is labelled and not quoted as a measurement.
  const spongeRate = hybrid ? opts.price!.spongeRate : H.spongeRate;
  const nPermChal = opts.preamble ? preambleChallengeCount(opts.preamble) : 0;
  const slots = slotLayout(shape, nPermChal, H);
  const deepCols = opts.deepCols ?? 128;
  /** ⚑ THE PRICE IS A PARAMETER so the SAME segment list can be costed at a
   *  different hash. `MINA-FACING-TERMINAL-OPTIONS`'s Pasta projection used to
   *  be a hand-scaled decomposition of a retired flat-height model; costing this
   *  walk at `priceAt(PASTA_HASH)` re-derives it from the real geometry
   *  instead, with the arithmetic terms provably untouched because they live in
   *  `ARITH_PRICE` and are shared by both tables. */
  const P = opts.price ?? PRICE;
  const K = shape.knobs;
  const segs: Segment[] = [];
  const reads: number[][] = [];
  const writes: number[][] = [];
  const push = (s: Segment, rd: number[], wr: number[]) => {
    segs.push(s);
    reads.push(rd);
    writes.push(wr);
  };

  /** The `DuplexChallenger` state machine as a segment emitter. Both the
   *  preamble and the FRI transcript run it; the ONLY differences are where the
   *  entering state comes from and whether the entering output buffer is live.
   *  ⚑ ONE emitter, because two would be two chances to get `sample`'s
   *  re-duplex condition subtly different. */
  const challengerRun = (
    entry: DuplexEntry,
    entryBufferLive: boolean,
    sampleSlots: (s: SampleRef) => number[],
    body: (io: { observe: (a: AbsorbRef) => void; sample: (s: SampleRef) => void }) => void,
  ) => {
    let inBuf: AbsorbRef[] = [];
    let outCount = entryBufferLive ? H.chalSqueeze : 0;
    let pending: SampleRef[] = [];
    let absorbed: AbsorbRef[] = [];
    let perm = false;
    let firstEntry = entry;
    const flush = () => {
      push(
        {
          t: 'duplex',
          absorbs: absorbed,
          samples: pending,
          perm,
          rows: perm ? P.perm : 64,
          entry: firstEntry,
        },
        segs.length === 0 ? [] : [...slots.chal],
        [...slots.chal, ...pending.flatMap(sampleSlots)],
      );
      absorbed = [];
      pending = [];
      firstEntry = 'carry';
    };
    let open = entryBufferLive;
    const duplex = () => {
      if (open) flush();
      absorbed = inBuf;
      inBuf = [];
      outCount = H.chalSqueeze;
      perm = true;
      open = true;
    };
    body({
      observe: (a: AbsorbRef) => {
        outCount = 0;
        inBuf.push(a);
        if (inBuf.length === H.chalAbsorbRate) duplex();
      },
      sample: (dst: SampleRef) => {
        if (inBuf.length > 0 || outCount === 0) duplex();
        outCount--;
        pending.push(dst);
      },
    });
    if (open) flush();
    if (inBuf.length !== 0)
      throw new Error(
        `the challenger run ended with ${inBuf.length} unabsorbed lanes — a segment list that ` +
          'drops them describes a different transcript',
      );
  };

  // ---- the batch-STARK PREAMBLE, when it is bound -------------------------
  //
  // ⚑ THIS IS §3.14 RESIDUAL 1. Without this block the walk's first segment
  // reads `ft.chalState` — a WITNESS, covered by `friDigest` and by nothing
  // else. A prover who picks it picks FRI's α, all 16 βs and all 19 query
  // indices, and the whole 11,303-segment walk then authenticates a transcript
  // nobody forced. With it, the entering state is the all-zero sponge of
  // `DuplexChallenger::new` — a literal — driven by the root's own commitments,
  // public values, cumulative sums and 2,630 opened values.
  if (opts.preamble) {
    const ops = preambleOps(shape, opts.preamble, H);
    challengerRun(
      'zero',
      false,
      (s) =>
        s.dst === 'permChal'
          ? [slots.permChal[s.i][s.lane]]
          : s.dst === 'airAlpha'
            ? [slots.airAlpha[s.lane]]
            : s.dst === 'zeta'
              ? [slots.zetaS[s.lane]]
              : [],
      ({ observe, sample }) => {
        for (const op of ops) (op.t === 'observe' ? observe(op.a) : sample(op.s));
      },
    );
    //  The closing equality. `ft` is not in scope here, so the lane numbers are
    //  recomputed from the same construction `friLaneTable` uses — asserted
    //  identical by `assertPreambleSealLanes` at the leg, because two
    //  independent numberings of one table is exactly the shape that drifts.
    const zetaAt = preambleZetaLanes(shape, H);
    const air = airColumnIndex();
    const { base } = permChalAssignment(opts.preamble);
    const chalAt: { at: number; chal: number }[] = [];
    opts.preamble.instances.forEach((inst, i) => {
      //  Instance `i`'s `j`-th lookup owns `challenge[C·j .. C·j+C)`, and those
      //  are the pair its bus was assigned.
      (base[i] ?? []).forEach((b, j) => {
        for (let c = 0; c < opts.preamble!.challengesPerLookup; c++) {
          const label = `${inst.name}|challenge[${opts.preamble!.challengesPerLookup * j + c}]`;
          const g = air.byLabel.get(label);
          if (g === undefined)
            throw new Error(`the AIR legend does not name \`${label}\` — the preamble seal cannot bind it`);
          chalAt.push({ at: g, chal: b + c });
        }
      });
    });
    push(
      {
        t: 'preSeal',
        zetaAt,
        chalAt,
        armed: opts.seal !== false,
        rows: (zetaAt.length + chalAt.length) * EXT_LANES * P.witnessLane,
      },
      [...slots.zetaS, ...slots.permChal.flat()],
      [],
    );
  }

  // ---- the FRI transcript -------------------------------------------------
  // The schedule is `verify_fri`'s, simulated so the duplex boundaries — the
  // only places a cut may fall inside the transcript — are compile-time facts.
  //
  // ⚑ THE TRANSCRIPT DOES NOT START EMPTY, AND STARTING IT EMPTY COSTS ONE
  // PERMUTATION AND THEREFORE EVERY CHALLENGE. `verify_fri` is entered with the
  // challenger's OUTPUT BUFFER ALREADY FULL — `two_adic_pcs::verify` has just
  // finished observing every opened evaluation, and the state the dumper
  // records carries `output_buffer = sponge_state[..8]`. So FRI's own `alpha` is
  // drawn by POPPING that buffer, with NO permutation, and a simulation that
  // duplexes first draws α from a state one permutation ahead — and then every
  // β, the PoW sample and all 19 query indices with it. This was measured, not
  // reasoned: the first slice to reach the 16-bit grind refused, because the
  // low bits of a sample from the wrong permutation are not zero.
  //  ⚑ The entering buffer is LIVE either way: the preamble ends on a rate
  //  boundary (its last absorb duplexes), so `verify_fri` is entered with a full
  //  output buffer whether that state was witnessed or derived. `entry` says
  //  which — and with a preamble the FRI transcript's first segment is no longer
  //  the walk's first, so `k === 0` would have silently pointed it at
  //  `ft.chalState` again.
  if (H.transcript === 'carried') {
    //  ⚑ ONE SEGMENT INSTEAD OF THE WHOLE DUPLEX RUN. The challenges are read
    //  from the committed table; the price is the range check on each lane plus
    //  the bit split that bounds each query index. Nothing is derived and the
    //  segment says so by its type.
    push(
      {
        t: 'chalCarry',
        rows:
          (EXT_LANES + K.layers * EXT_LANES) * P.witnessLane +
          K.numQueries * (P.witnessLane + K.indexBits * P.witnessLane),
      },
      [],
      [...slots.alpha, ...slots.beta.flat(), ...slots.qidx],
    );
  } else
  challengerRun(
    opts.preamble ? 'carry' : 'chalState',
    true,
    (s: SampleRef): number[] => {
      if (s.dst === 'alpha') return [slots.alpha[s.lane]];
      if (s.dst === 'beta') return [slots.beta[s.layer][s.lane]];
      if (s.dst === 'qidx') return [slots.qidx[s.query]];
      return [];
    },
    ({ observe, sample }) => {
      for (let l = 0; l < EXT_LANES; l++) sample({ dst: 'alpha', lane: l });
      for (let r = 0; r < K.layers; r++) {
        for (let j = 0; j < H.digestLanes; j++) observe({ src: 'commit', layer: r, lane: j });
        //  commit_pow_bits = 0: `check_witness` returns BEFORE observing.
        for (let l = 0; l < EXT_LANES; l++) sample({ dst: 'beta', layer: r, lane: l });
      }
      for (let i = 0; i < K.finalPolyLen; i++)
        for (let l = 0; l < EXT_LANES; l++) observe({ src: 'finalPoly', i, lane: l });
      for (let r = 0; r < K.layers; r++) observe({ src: 'arity' });
      //  query_pow_bits = 16: the witness IS observed, and the next sample's low
      //  16 bits are forced to zero. That sample is charged to its duplex.
      observe({ src: 'pow' });
      sample({ dst: 'pow' });
      for (let q = 0; q < K.numQueries; q++) sample({ dst: 'qidx', query: q });
    },
  );

  // ---- the permutation round's bridge to the AIR half, once ---------------
  {
    const pi = shape.rounds.findIndex((r) => r.name === 'permutation');
    if (pi >= 0)
      shape.rounds[pi].matrices.forEach((m, mi) => {
        const nk = m.width / EXT_LANES;
        for (let p = 0; p < m.numPoints; p++)
          for (let a = 0; a < nk; a += 32)
            push(
              {
                t: 'permBind',
                mat: mi,
                point: p,
                from: a,
                to: Math.min(a + 32, nk),
                rows: (Math.min(a + 32, nk) - a) * (3 * P.extAdd + 5 * EXT_LANES * P.witnessLane),
              },
              [],
              [],
            );
      });
  }

  // ---- the queries --------------------------------------------------------
  const lgmh = K.logGlobalMaxHeight;
  for (let q = 0; q < K.numQueries; q++) {
    const idxSlot = [slots.qidx[q]];

    // -- the input-phase openings, one per PCS round.
    shape.rounds.forEach((round, ri) => {
      const hs = roundHeights(round);
      const top = hs[0];
      // Every height's opened rows are sponged; the tallest seeds `cur`, the
      // rest wait to be injected at the level their height names.
      for (const h of hs) {
        const hi = shape.heights.indexOf(h);
        const w = rowWidthAt(round, h);
        const nb = ceilDiv(w, spongeRate);
        for (let b = 0; b < nb; b++) {
          const lanes = Math.min(spongeRate, w - b * spongeRate);
          const first = b === 0;
          const last = b === nb - 1;
          const seeds = h === top;
          push(
            {
              t: 'inBlock',
              q,
              round: ri,
              height: h,
              block: b,
              lanes,
              first,
              last,
              seeds,
              rows: P.perm + lanes * P.witnessLane,
            },
            first ? [] : [...slots.sponge],
            last ? [...(seeds ? slots.cur : slots.inj[hi])] : [...slots.sponge],
          );
        }
      }
      // `MerkleTreeMmcs::verify_batch`: `top` levels of compress against the
      // witnessed siblings, with the shorter matrices' digests compressed in at
      // the level whose padded height they match.
      for (let lv = 0; lv < top; lv++) {
        const nextH = top - 1 - lv;
        const inject = hs.includes(nextH) ? nextH : null;
        push(
          {
            t: 'inLevel',
            q,
            round: ri,
            level: lv,
            inject,
            rows: P.merkleLevel + (inject === null ? 0 : P.merkleInject),
          },
          [
            ...slots.cur,
            ...idxSlot,
            ...(inject === null ? [] : slots.inj[shape.heights.indexOf(inject)]),
          ],
          [...slots.cur],
        );
      }
      push({ t: 'inRoot', q, round: ri, rows: 8 }, [...slots.cur], []);
    });

    // -- the DEEP quotient. The accumulator and `alpha_pow` are keyed by
    //    HEIGHT and advance in ENCOUNTER order across rounds, which is the
    //    convention a per-matrix counter gets wrong.
    //
    //    ⚑ THE COLUMN RUN IS SUBDIVIDED, AND IT MUST BE. The widest matrix is
    //    452 columns, which at 49 rows a Horner step plus the range checks on
    //    the opened value is ~34,000 rows — a segment that fits in a step only
    //    if it is alone in one. Horner runs from the TOP column DOWN, so a run
    //    splits cleanly into descending column ranges with the accumulator
    //    crossing in `dh`; `open` seeds it and `close` computes `1/(z − x)` and
    //    folds it into the height's slot.
    push(
      { t: 'deepInit', q, rows: 0 },
      [],
      [...shape.heights.flatMap((_, hi) => [...slots.dacc[hi], ...slots.dpow[hi]])],
    );
    shape.rounds.forEach((round, ri) => {
      round.matrices.forEach((m, mi) => {
        const hi = shape.heights.indexOf(m.logHeight);
        for (let p = 0; p < m.numPoints; p++) {
          const cuts: [number, number][] = [];
          for (let hiCol = m.width; hiCol > 0; hiCol -= deepCols)
            cuts.push([Math.max(0, hiCol - deepCols), hiCol]);
          cuts.forEach(([a, b], ci) => {
            const open = ci === 0;
            const close = a === 0;
            push(
              {
                t: 'deep',
                q,
                round: ri,
                mat: mi,
                point: p,
                from: a,
                to: b,
                open,
                close,
                rows:
                  (close ? P.extInverse + 2 * P.extMul + P.extAdd : 0) +
                  (b - a) * (P.horner + EXT_LANES * P.witnessLane),
              },
              [
                ...slots.alpha,
                ...(open ? [] : slots.dh),
                ...(close ? [...slots.dacc[hi], ...slots.dpow[hi]] : []),
                ...idxSlot,
              ],
              close ? [...slots.dacc[hi], ...slots.dpow[hi]] : [...slots.dh],
            );
          });
        }
      });
    });
    // The reduced openings become the chain's `initial` and its roll-ins.
    //  ⚑ `mat < 0` marks the segment that PUBLISHES one height's reduced
    //  opening: the tallest becomes the fold chain's `initial`, the rest its
    //  roll-ins. `point` carries the height index — `verify_query` REFUSES a
    //  proof whose first reduced opening is at any height but the global max,
    //  and this is where that ordering is fixed.
    shape.heights.forEach((h, hi) => {
      push(
        { t: 'deep', q, round: -1, mat: -1, point: hi, from: 0, to: 0, open: false, close: false, rows: 4 },
        [...slots.dacc[hi]],
        [...(hi === 0 ? slots.folded : slots.ro[hi])],
      );
    });

    // -- the fold chain.
    for (let r = 0; r < K.layers; r++) {
      const depth = lgmh - 1 - r;
      //  ⚑ THE ROW, THE LEAF AND THE FOLD ARE ONE SEGMENT, AND THAT IS FORCED.
      //  `fold_row` consumes the same `[even, odd]` pair the leaf hash commits
      //  to, and that pair is built from the running fold value and a WITNESSED
      //  sibling. Split across a cut, the folding half would re-witness the
      //  sibling and nothing would tie it to the one the leaf hashed — a splice
      //  that every Merkle check in the walk still passes. So the sibling is
      //  read once, by one segment, and never crosses.
      push(
        {
          t: 'cpLeaf',
          q,
          r,
          rows: P.perm + EXT_LANES * P.witnessLane + P.foldRow + P.descent,
        },
        [...slots.folded, ...slots.beta[r], ...idxSlot, ...(r === 0 ? [] : [slots.x])],
        [...slots.cur, ...slots.folded, slots.x],
      );
      for (let lv = 0; lv < depth; lv++)
        push({ t: 'cpLevel', q, r, level: lv, rows: P.merkleLevel }, [...slots.cur, ...idxSlot], [
          ...slots.cur,
        ]);
      push({ t: 'cpRoot', q, r, rows: 8 }, [...slots.cur], []);
      const rollHeight = shape.heights.indexOf(lgmh - 1 - r);
      const rollIn = rollHeight > 0 ? rollHeight : null;
      if (rollIn !== null)
        push(
          { t: 'cpFold', q, r, rollIn, rows: P.rollIn },
          [...slots.folded, ...slots.beta[r], ...slots.ro[rollIn]],
          [...slots.folded],
        );
    }
    push({ t: 'final', q, rows: P.extAdd + 8 }, [...slots.folded, ...idxSlot], []);
  }

  // ---- liveness, backwards ------------------------------------------------
  const liveIn: number[][] = new Array(segs.length + 1);
  let live = new Set<number>();
  liveIn[segs.length] = [];
  for (let k = segs.length - 1; k >= 0; k--) {
    for (const w of writes[k]) live.delete(w);
    for (const r of reads[k]) live.add(r);
    liveIn[k] = [...live].sort((a, b) => a - b);
  }

  return {
    shape,
    hash: H,
    priced: hybrid ? 'price-only' : 'shaped',
    slots,
    segs,
    reads,
    writes,
    liveIn,
    totalRows: segs.reduce((a, s) => a + s.rows, 0),
  };
}

// ===========================================================================
// 6. The planner.
// ===========================================================================

export type FriSlice = {
  index: number;
  /** Segments `[from, to)`. */
  from: number;
  to: number;
  /** Slots crossing IN and OUT. */
  liveIn: number[];
  liveOut: number[];
  /** AIR-side and FRI-side column chunks this slice must load. */
  readsAirChunks: number[];
  readsFriChunks: number[];
  workRows: number;
  carryRows: number;
};

export type FriPlan = {
  slices: FriSlice[];
  nAirChunks: number;
  nFriChunks: number;
  chunkSize: number;
  totalWork: number;
  totalCarry: number;
};

/** Which committed lanes a segment reads, split by which commitment holds them.
 *  Everything else a segment touches — Merkle siblings, path digests — is
 *  self-authenticating and is not here. */
export function segmentReads(
  w: SegmentedWalk,
  op: OpenedPlan,
  ft: FriLaneTable,
  k: number,
): { air: number[]; fri: number[] } {
  const s = w.segs[k];
  const air: number[] = [];
  const air2 = air;
  const fri: number[] = [];
  const range = (a: number, b: number, into: number[]) => {
    for (let i = a; i < b; i++) into.push(i);
  };
  switch (s.t) {
    case 'duplex':
      //  ⚑ ONLY a `chalState` duplex loads the entering state from the
      //  commitment; a `carry` one takes it from the carry and a `zero` one from
      //  a literal. A slice that re-witnessed it would be starting a fresh
      //  transcript in the middle of one. (This tested `k === 0` until the
      //  preamble landed, and `k === 0` is now the preamble's first segment.)
      if (s.entry === 'chalState') range(ft.chalState, ft.chalState + w.hash.chalStateLanes, fri);
      for (const a of s.absorbs) {
        if (a.src === 'commit') fri.push(ft.commit[a.layer] + a.lane);
        else if (a.src === 'finalPoly') fri.push(ft.finalPoly[a.i] + a.lane);
        else if (a.src === 'pow') fri.push(ft.powWitness);
        else if (a.src === 'roundCommit') fri.push(ft.inputCommit[a.round] + a.lane);
        else if (a.src === 'publicValue') air.push(a.at * EXT_LANES);
        else if (a.src === 'cumSum') air.push(a.at * EXT_LANES + a.lane);
        else if (a.src === 'opened') {
          const r = op.refs[a.round][a.mat][a.point][a.col];
          if (r.where === 'air') air.push(r.at * EXT_LANES + a.lane);
          else fri.push(r.at + a.lane);
        }
        //  `shape` and `arity` are literals and read nothing.
      }
      break;
    case 'chalCarry': {
      const c = w.hash.transcript === 'carried' ? ft.carried : null;
      if (c === null)
        throw new Error(
          'a `chalCarry` segment over a lane table with no carried-challenge region — the walk and ' +
            'the table were built at different transcript modes',
        );
      range(c.friAlpha, c.friAlpha + EXT_LANES, fri);
      for (const b of c.betas) range(b, b + EXT_LANES, fri);
      for (const q of c.qidx) fri.push(q);
      break;
    }
    case 'preSeal':
      //  ζ, against the point-0 lane of EVERY committed matrix — the point both
      //  halves open at.
      for (const z of s.zetaAt) range(z, z + EXT_LANES, fri);
      //  The LogUp challenges, against the AIR chain's own `challenge[k]`.
      for (const c of s.chalAt) range(c.at * EXT_LANES, (c.at + 1) * EXT_LANES, air);
      break;
    case 'inBlock': {
      const [a, b] = ft.blockLanes(s.q, s.round, s.height, s.block);
      range(a, b, fri);
      break;
    }
    case 'inRoot':
      range(ft.inputCommit[s.round], ft.inputCommit[s.round] + w.hash.digestLanes, fri);
      break;
    case 'cpRoot':
      range(ft.commit[s.r], ft.commit[s.r] + w.hash.digestLanes, fri);
      break;
    case 'final':
      for (const o of ft.finalPoly) range(o, o + EXT_LANES, fri);
      break;
    case 'permBind': {
      const pi = w.shape.rounds.findIndex((r) => r.name === 'permutation');
      const m = w.shape.rounds[pi].matrices[s.mat];
      const cols = op.refs[pi][s.mat][s.point];
      const t = dagTableName(m.name);
      const air = airColumnIndex();
      for (let k = s.from; k < s.to; k++) {
        const e = air.byLabel.get(`${t}|perm[${s.point}][${k}]`);
        if (e === undefined) throw new Error(`the AIR legend has no perm[${s.point}][${k}] for ${t}`);
        range(e * EXT_LANES, (e + 1) * EXT_LANES, air2);
        for (let j = 0; j < EXT_LANES; j++) {
          const r = cols[k * EXT_LANES + j];
          range(r.at, r.at + EXT_LANES, fri);
        }
      }
      break;
    }
    case 'deep': {
      if (s.mat < 0) break;
      //  f(x): the opened row, always FRI-side.
      const base = ft.fx[s.q][s.round][s.mat];
      range(base + s.from, base + s.to, fri);
      //  f(z): AIR-side wherever the legend names it.
      const cols = op.refs[s.round][s.mat][s.point];
      for (let c = s.from; c < s.to; c++) {
        const r = cols[c];
        if (r.where === 'air') range(r.at * EXT_LANES, (r.at + 1) * EXT_LANES, air);
        else range(r.at, r.at + EXT_LANES, fri);
      }
      //  z, on the segment that closes the run and forms `1/(z − x)`.
      if (s.close) {
        const zo = ft.z[s.round][s.mat][s.point];
        range(zo, zo + EXT_LANES, fri);
      }
      break;
    }
    default:
      break;
  }
  return { air, fri };
}

/**
 * **THE PLANNER.** Greedy-maximal slices under a row budget, exactly as
 * `planRootAirChain` cuts the AIR: extend while work + carry fits, then cut.
 *
 * ⚑ THE GREEDY CHOICE IS MEASURED HERE, NOT INHERITED. This planner took
 * `planRootAirChain`'s shape AND its justification — "there is no such cliff
 * here" — which was established for the AIR DAG's carry, bounded by a cut width
 * of 102, and is NOT established for this walk, whose carry spread is 6.5x.
 * `npm run cost-gate` phase [5] runs a dynamic program over this exact carry
 * function: at the deployed 50,000-row budget both give **839 slices**, and the
 * DP recovers 260,065 rows of carry (2.8%) at the same count. So greedy costs
 * nothing in slices at this budget — which is a measurement, and it is the
 * reason to keep the greedy planner rather than the borrowed sentence.
 *
 * The carry is recomputed at every candidate end because it is a function of
 * the CUT rather than of the slice's length — a boundary that falls inside a
 * DEEP run carries five height accumulators and their `alpha_pow`s; one that
 * falls between two queries carries almost nothing but the derived challenges.
 * That spread is the whole reason a boundary here is not a constant, and §3.20
 * measured its two ends at 34,566 and 762 rows.
 */
export function planFriWalk(
  w: SegmentedWalk,
  op: OpenedPlan,
  ft: FriLaneTable,
  opts: { usableRows: number; chunkLanes: number; maxSlices?: number },
): FriPlan {
  const chunkSize = opts.chunkLanes;
  const air = airColumnIndex();
  const nAirChunks = Math.ceil(((air.nBase + air.nExt) * EXT_LANES) / chunkSize);
  const nFriChunks = Math.max(1, Math.ceil(ft.nLanes / chunkSize));
  /** A chunk digest costs one witnessed lane's worth of range check plus the
   *  Poseidon over it; the AIR chain charges both at `WITNESS_ROWS_PER_VALUE`
   *  per extension value and this mirrors that. */
  const DIGEST_ROWS = PRICE.witnessLane * EXT_LANES;
  const slices: FriSlice[] = [];
  let from = 0;
  while (from < w.segs.length) {
    let work = 0;
    const airSet = new Set<number>();
    const friSet = new Set<number>();
    let best = -1;
    let bestCarry = 0;
    let bestWork = 0;
    let bestAir: number[] = [];
    let bestFri: number[] = [];
    let to = from;
    while (to < w.segs.length) {
      work += w.segs[to].rows;
      const rd = segmentReads(w, op, ft, to);
      for (const l of rd.air) airSet.add(Math.floor(l / chunkSize));
      for (const l of rd.fri) friSet.add(Math.floor(l / chunkSize));
      to++;
      const carry =
        (w.liveIn[from].length + w.liveIn[to].length) * PRICE.witnessLane +
        (airSet.size + friSet.size) * chunkSize * PRICE.witnessLane +
        (nAirChunks + nFriChunks) * DIGEST_ROWS;
      if (work + carry > opts.usableRows) {
        to--;
        work -= w.segs[to].rows;
        break;
      }
      best = to;
      bestCarry = carry;
      bestWork = work;
      bestAir = [...airSet].sort((a, b) => a - b);
      bestFri = [...friSet].sort((a, b) => a - b);
    }
    if (best <= from)
      throw new Error(
        `no slice fits at segment ${from} (${w.segs[from].t}, ${Math.round(w.segs[from].rows)} rows) ` +
          `plus its carry, under ${opts.usableRows} rows`,
      );
    slices.push({
      index: slices.length,
      from,
      to: best,
      liveIn: w.liveIn[from],
      liveOut: w.liveIn[best],
      readsAirChunks: bestAir,
      readsFriChunks: bestFri,
      workRows: bestWork,
      carryRows: bestCarry,
    });
    from = best;
    if (opts.maxSlices && slices.length >= opts.maxSlices) break;
  }
  return {
    slices,
    nAirChunks,
    nFriChunks,
    chunkSize,
    totalWork: slices.reduce((a, s) => a + s.workRows, 0),
    totalCarry: slices.reduce((a, s) => a + s.carryRows, 0),
  };
}

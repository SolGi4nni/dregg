import { Field, Struct } from 'o1js';
import { canonicalLane } from './Poseidon2BabyBearW16.js';
import { LANES_PER_FIELD, packLanes } from './RootAirChain.js';
import { AirColumnIndex, EXT_LANES } from './RootFriWalk.js';

// ---------------------------------------------------------------------------
// THE CLAIM — what the chain is a proof OF, carried out of it.
//
// ⚑ THE DISEASE THIS CLOSES IS THE ARC'S THIRD INSTANCE OF ONE SHAPE. A
// prover-chosen value feeds everything downstream and nothing forces it. First
// the fold chain's `initial` (§3.15, closed by the DEEP quotient binding), then
// the challenger state entering FRI (§3.29, closed by deriving it from the
// batch's own commitments). Now the identity of the proof itself: every
// statement the chain makes is relative to `dagDigest` and `friDigest`, which
// are digests of lane tables THE PROVER SUPPLIES, and slice 0 enters a genesis
// constant. A Mina-side verifier handed the whole chain learns "*some* batch of
// seven AIRs with these column digests verifies" — not "dregg's root proof, for
// chain head H, over N turns, verifies".
//
// ⚑ AND THE CLAIM IS ALREADY IN THE LANE TABLE. `expose_claim`'s 25 public
// values ARE the chain claim: `[first_old8 ‖ last_new8 ‖ count ‖ acc_0..7]`
// (`circuit-prove/src/ivc_turn_chain.rs:278,343-368`), and the Rust host's own
// segment tooth compares exactly that vector against `[genesis_root8 ‖
// final_root8 ‖ num_turns ‖ chain_digest]` (`:3096-3115`). The preamble already
// ABSORBS all 25 into the transcript (§3.29), so bending one moves ζ and the
// preamble seal refuses. What was missing is not a binding of the lanes to the
// proof — it is the lanes coming OUT, where a verifier can read them.
//
// ⚑ SO THIS IS NOT A NEW WITNESS, AND THAT IS THE WHOLE POINT. The claim a slice
// exposes is read through the SAME chunk accessor the walk reads every AIR-held
// opened value with, out of chunks whose digests are spliced into `dagDigest`,
// which `Poseidon(dagDigest, friDigest) == publicInput` already pins. Replacing
// one prover-chosen value with another would be this campaign's failure mode,
// not its fix.
// ---------------------------------------------------------------------------

const LANE_MAX = (1n << 31n) - 1n;

// ===========================================================================
// 1. The layout — mirrored from the Rust that emits it, field for field.
// ===========================================================================

/** `SEG_ANCHOR_WIDTH` — the 8-felt (~124-bit) state anchor. */
export const SEG_ANCHOR_WIDTH = 8;
/** `SEG_DIGEST_WIDTH` — the ordered-history commitment, 8 felts. */
export const SEG_DIGEST_WIDTH = 8;
/** `SEG_FIRST_OLD` — lane 0, the genesis state root. */
export const SEG_FIRST_OLD = 0;
/** `SEG_LAST_NEW` — lane 8, the final state root. */
export const SEG_LAST_NEW = SEG_ANCHOR_WIDTH;
/** `SEG_COUNT` — lane 16, `num_turns`. ⚑ ONE lane, and it is the field a
 *  verifier reads without unpacking anything. */
export const SEG_COUNT = 2 * SEG_ANCHOR_WIDTH;
/** `SEG_DIGEST_FIRST` — lane 17, `acc_0`. */
export const SEG_DIGEST_FIRST = 2 * SEG_ANCHOR_WIDTH + 1;
/** `NUM_CHAIN_CLAIMS = SEG_DIGEST_FIRST + SEG_DIGEST_WIDTH` — 25.
 *  `circuit-prove/src/ivc_turn_chain.rs:278`. */
export const NUM_CHAIN_CLAIMS = SEG_DIGEST_FIRST + SEG_DIGEST_WIDTH;

/**
 * **WHAT THE CHAIN SAYS IT PROVED.** Four Pasta field elements, three of them a
 * BabyBear octet packed losslessly at 31 bits a lane (`packLanes`, 248 of 254
 * bits) and one of them a small integer a verifier reads directly.
 *
 * ⚑ PACKED SEMANTICALLY, NOT POSITIONALLY. `packLanes` over the flat 25 would
 * cut fields at lanes 0-7 / 8-15 / 16-23 / 24 and the third would straddle
 * `num_turns` and seven digest lanes — a field with no name. Packing each named
 * block on its own boundary costs the same four fields and means a Mina-side
 * verifier compares `finalRoot` against the head it was told about rather than
 * against a window.
 *
 * ⚑ THE PACKING IS INJECTIVE ONLY ON CANONICAL LANES, which is why
 * `readClaimLanes` range-checks all 25 rather than inheriting the check.
 */
export class ChainClaim extends Struct({
  /** `packLanes(first_old8)` — the state root the chain starts from. */
  genesisRoot: Field,
  /** `packLanes(last_new8)` — the state root it ends at. */
  finalRoot: Field,
  /** `count` — how many turns the chain folds. One BabyBear lane, unpacked. */
  numTurns: Field,
  /** `packLanes(acc_0..acc_7)` — the ordered-history commitment. */
  chainDigest: Field,
}) {}

/**
 * A slice's public output once the chain carries its claim: the boundary the
 * next slice enters, and the claim every slice in the chain agrees on.
 *
 * ⚑ THE BOUNDARY FIELD IS BYTE-FOR-BYTE THE ONE §3.29 EMITTED. The claim is
 * ADDED beside it, not folded into it — a claim folded into the seal preimage
 * would still leave the terminal proof stating a hash, and a verifier would have
 * to be handed the claim to check it. Carried in the clear, the terminal proof
 * STATES it.
 */
export class ClaimedBoundary extends Struct({
  boundary: Field,
  claim: ChainClaim,
}) {}

// ===========================================================================
// 2. Where the claim lives — resolved against the AIR legend, never guessed.
// ===========================================================================

export type ClaimIndex = {
  /** The 25 AIR extension indices of `expose_claim|public[i]`, in claim order. */
  at: number[];
  /** ⚑ The BASE lane of each — `4·at`, ONE lane, not four. A public value is a
   *  base field element; `verify_batch` absorbs it as such (`RootFriWalk`'s
   *  `publicValue` absorb reads lane `4·at` alone) and the other three lanes of
   *  the extension slot are zero. Reading four would decode a different claim
   *  out of numbers that are all present and all correct. */
  lanes: number[];
};

/**
 * Resolve the claim against the AIR chain's own column legend.
 *
 * ⚑ A MISSING LABEL IS A FAILURE, NOT A FALLBACK. If the legend does not name
 * `expose_claim|public[i]` then the claim is not under `dagDigest`, and a chain
 * that carried it anyway would be carrying a fresh witness — exactly the thing
 * this module exists to not do.
 */
export function claimIndex(air: AirColumnIndex): ClaimIndex {
  const at: number[] = [];
  for (let i = 0; i < NUM_CHAIN_CLAIMS; i++) {
    const label = `expose_claim|public[${i}]`;
    const g = air.byLabel.get(label);
    if (g === undefined)
      throw new Error(
        `the AIR legend does not name \`${label}\` — the chain's claim is not under \`dagDigest\` ` +
          'and carrying it would mean witnessing it, which is the hole this closes',
      );
    at.push(g);
  }
  return { at, lanes: at.map((g) => g * EXT_LANES) };
}

/** The AIR column chunks a slice must have loaded to read the whole claim. */
export const claimChunks = (ix: ClaimIndex, chunkLanes: number): number[] =>
  [...new Set(ix.lanes.map((l) => Math.floor(l / chunkLanes)))].sort((a, b) => a - b);

/**
 * **THE BINDING SLICE.** The first slice of a plan whose loaded AIR chunks cover
 * every claim lane.
 *
 * ⚑ THE BINDING GOES WHERE THE CHUNKS ALREADY ARE. Choosing a slice and then
 * adding the chunks it needs would move the planner's carry, and the plan is
 * what 905 instances / 131 programs is a measurement of. Measured at the root's
 * real geometry the claim lands in AIR chunks 17 and 18, and head slice 1
 * already loads both — so the binding is free in chunk loads and the plan does
 * not move at all.
 */
export function claimBindSlice(
  slices: { readsAirChunks: number[] }[],
  chunks: number[],
): number {
  return slices.findIndex((s) => chunks.every((c) => s.readsAirChunks.includes(c)));
}

/**
 * Read lane `g` out of the chunk-major array a slice loaded.
 *
 * ⚑ THIS REPEATS `runSegments`'s OWN accessor, deliberately and visibly, because
 * the alternative is exporting a closure out of the interpreter. Two numberings
 * of one table is the shape that drifts (`assertPreambleSealLanes` exists for
 * the same reason), so the leg cross-checks this against the raw lane array
 * before any circuit runs.
 */
export function laneOfChunks<T>(
  readsChunks: number[],
  chunkLanes: number,
  loaded: T[],
  g: number,
): T {
  const c = Math.floor(g / chunkLanes);
  const at = readsChunks.indexOf(c);
  if (at < 0)
    throw new Error(
      `the claim needs AIR lane ${g} (chunk ${c}) and this slice loaded chunks [${readsChunks}] — ` +
        'the binding slice must be one that already reads the claim',
    );
  return loaded[at * chunkLanes + (g - c * chunkLanes)];
}

// ===========================================================================
// 3. The claim, in circuit.
// ===========================================================================

/** Pack one BabyBear octet into one Pasta field, `packLanes`'s 31-bit layout. */
function octet(lanes: Field[]): Field {
  if (lanes.length !== LANES_PER_FIELD)
    throw new Error(`an anchor is ${LANES_PER_FIELD} lanes and this one is ${lanes.length}`);
  return packLanes(lanes)[0];
}

/** The out-of-circuit twin of `octet`. */
export function octetBigInt(lanes: bigint[]): bigint {
  if (lanes.length !== LANES_PER_FIELD)
    throw new Error(`an anchor is ${LANES_PER_FIELD} lanes and this one is ${lanes.length}`);
  return lanes.reduce((a, v, j) => a + v * (1n << (31n * BigInt(j))), 0n);
}

/** The 25 claim lanes, read out of a slice's loaded AIR chunks and
 *  range-checked. */
export function readClaimLanes(
  ix: ClaimIndex,
  readsChunks: number[],
  chunkLanes: number,
  airLanes: Field[],
): Field[] {
  return ix.lanes.map((g) =>
    //  ⚑ RANGE-CHECKED HERE RATHER THAN INHERITED. `chunkedCommitment` already
    //  canonicalises every loaded lane, so these 25 checks are redundant TODAY.
    //  They are not free (25 lanes out of 42 million rows) and they are kept
    //  because the packing below is injective only on canonical lanes, and an
    //  injectivity that depends on a check in another function is one that a
    //  refactor deletes silently.
    canonicalLane(laneOfChunks(readsChunks, chunkLanes, airLanes, g), LANE_MAX),
  );
}

/** The claim those 25 lanes denote. */
export function claimOfLanes(lanes: Field[]): ChainClaim {
  if (lanes.length !== NUM_CHAIN_CLAIMS)
    throw new Error(`a claim is ${NUM_CHAIN_CLAIMS} lanes and this one is ${lanes.length}`);
  return new ChainClaim({
    genesisRoot: octet(lanes.slice(SEG_FIRST_OLD, SEG_FIRST_OLD + SEG_ANCHOR_WIDTH)),
    finalRoot: octet(lanes.slice(SEG_LAST_NEW, SEG_LAST_NEW + SEG_ANCHOR_WIDTH)),
    numTurns: lanes[SEG_COUNT],
    chainDigest: octet(lanes.slice(SEG_DIGEST_FIRST, SEG_DIGEST_FIRST + SEG_DIGEST_WIDTH)),
  });
}

/** The out-of-circuit twin — what the leg decodes before anything compiles. */
export function claimOfLanesBigInt(lanes: bigint[]): {
  genesisRoot: bigint;
  finalRoot: bigint;
  numTurns: bigint;
  chainDigest: bigint;
} {
  if (lanes.length !== NUM_CHAIN_CLAIMS)
    throw new Error(`a claim is ${NUM_CHAIN_CLAIMS} lanes and this one is ${lanes.length}`);
  return {
    genesisRoot: octetBigInt(lanes.slice(SEG_FIRST_OLD, SEG_FIRST_OLD + SEG_ANCHOR_WIDTH)),
    finalRoot: octetBigInt(lanes.slice(SEG_LAST_NEW, SEG_LAST_NEW + SEG_ANCHOR_WIDTH)),
    numTurns: lanes[SEG_COUNT],
    chainDigest: octetBigInt(lanes.slice(SEG_DIGEST_FIRST, SEG_DIGEST_FIRST + SEG_DIGEST_WIDTH)),
  };
}

/**
 * **THE CLAIM SEAL.** The carried claim IS the `expose_claim` lanes under
 * `dagDigest`.
 *
 * ⚑ FOUR EQUALITIES, AND THEY ARE THE ONLY PLACE THE CLAIM STOPS BEING FREE.
 * Everything else in the carry is propagation. `armed = false` builds the
 * UNSEALED CONTROL: identical widths, identical chunk loads, identical lane
 * reads, identical range checks — only these four assertions removed. That is
 * what makes a refusal attributable to the seal rather than to the forged claim
 * being malformed somewhere else.
 */
export function assertClaimSeal(carried: ChainClaim, read: ChainClaim, armed = true) {
  if (!armed) return;
  carried.genesisRoot.assertEquals(read.genesisRoot);
  carried.finalRoot.assertEquals(read.finalRoot);
  carried.numTurns.assertEquals(read.numTurns);
  carried.chainDigest.assertEquals(read.chainDigest);
}

/**
 * The claim crosses a boundary unchanged.
 *
 * ⚑ WHY THIS IS AN EQUALITY AND NOT A HASH. The boundary `Field` already chains
 * by collision resistance and the claim could have ridden in its preimage — but
 * then a slice would have to be HANDED the claim to check the boundary, and the
 * terminal proof would state a hash of it. Four `assertEquals` a slice is the
 * price of the claim being readable at every link, and it is 4 constraints
 * against a ~47,000-row slice.
 */
export function assertClaimCarried(prev: ChainClaim, cur: ChainClaim) {
  prev.genesisRoot.assertEquals(cur.genesisRoot);
  prev.finalRoot.assertEquals(cur.finalRoot);
  prev.numTurns.assertEquals(cur.numTurns);
  prev.chainDigest.assertEquals(cur.chainDigest);
}

/**
 * How a slice participates in the claim carry — a COMPILE-TIME fact, so a
 * verifier reading the protocol knows which position seals and which propagate.
 */
export type ClaimCarry = {
  ix: ClaimIndex;
  /** TRUE on the ONE slice whose loaded chunks cover every claim lane. */
  seals: boolean;
  /** ⚑ FALSE builds the UNSEALED control (see `assertClaimSeal`). */
  armed?: boolean;
};

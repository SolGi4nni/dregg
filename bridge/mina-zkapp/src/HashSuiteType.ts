import type { Bool, Field } from 'o1js';

// ---------------------------------------------------------------------------
// ONE VERIFIER, TWO HASHES — the interface that keeps them from becoming two
// verifiers.
//
// ⚑ THE FAILURE THIS FILE EXISTS TO PREVENT, NAMED. dregg can mint a terminal
// proof under either `DreggStarkConfig` (Poseidon2 over BabyBear, what the root
// commits with today) or `DreggMinaConfig` (kimchi's Poseidon over Pasta Fp, the
// Mina-facing terminal). Both are real objects and the o1js side has to be able
// to verify either. The obvious way to get there is a second copy of the walk
// with the hash calls swapped — and this repo has a named class for exactly that
// outcome: two shapes that agree today and disagree later. Every fix to the DEEP
// quotient, the roll-in schedule, the transcript order or the AIR closing
// equality would then have to be made twice, and the second one is the one that
// gets forgotten.
//
// So the hash is a PARAMETER. `DreggProofVerify`'s query walk, transcript
// derivation, DEEP quotient and fold chain have exactly ONE implementation, and
// what varies is this record. The two implementations of it —
// `Poseidon2Merkle.babyBearMerkleSuite` + `FriChallenger.Challenger`, and
// `PastaMmcs.pastaMerkleSuite` + `PastaChallenger` — are each about a hundred
// lines and share no protocol logic at all.
//
// ⚑ THIS FILE HAS NO RUNTIME IMPORTS, and that is structural rather than tidy:
// `FriQueryStep` needs the Merkle half, `FriChallenger` needs `FriQueryStep`,
// and a suite record that pulled the challenger in would close that loop. The
// suite is therefore SPLIT — `MerkleSuite` is everything the fold chain needs,
// `HashSuite` adds the transcript — and `HashSuites.ts` (a leaf) assembles the
// two full ones.
// ---------------------------------------------------------------------------

/** Every digest in this codebase is a fixed-length array of native `Field`s:
 *  eight BabyBear lanes, or one Pasta element. The walk above only ever needs
 *  the lanes to compare two digests, so that is all the interface exposes. */
export type Digestish = { limbs: Field[] };

/**
 * The leaf sponge, splittable. See `MerkleSuite.spongeStream` for why this is a
 * separate object from `sponge` and what the two do not share.
 */
export type SpongeStream<D extends Digestish = Digestish> = {
  /** Field elements the running state occupies — 16 BabyBear lanes, 3 Pasta. */
  stateLanes: number;
  /** BabyBear lanes absorbed per permutation — 8 BabyBear, 16 Pasta. */
  rate: number;
  init(): Field[];
  /** Absorb up to `rate` row lanes. `lanesAlreadyChecked` has the same two real
   *  call sites `sponge`'s does. */
  absorb(state: Field[], row: Field[], lanesAlreadyChecked?: boolean): Field[];
  finish(state: Field[]): D;
  initBigInt(): bigint[];
  absorbBigInt(state: bigint[], row: bigint[]): bigint[];
  finishBigInt(state: bigint[]): bigint[];
};

/** The MMCS half — the hash, the digest, and the Merkle step. */
export type MerkleSuite<D extends Digestish = Digestish> = {
  /** For error messages and for the fixture's `hash` field to be checked
   *  against, so a Pasta fixture fed to the BabyBear walk fails by NAME rather
   *  than by an opaque digest mismatch forty thousand rows later. */
  name: string;
  /** `1` for Pasta, `8` for BabyBear. */
  digestElems: number;
  /** The provable type, for `Provable.Array(suite.Digest, n)`. */
  Digest: any;
  zero(): D;
  from(v: bigint[]): D;
  /** Range-check a WITNESSED digest. Empty for Pasta — every `Field` is already
   *  a Pasta element — and eight lane checks for BabyBear, without which its
   *  bound tracking is a claim about numbers nothing forces to be small. */
  assertInRange(d: D): void;
  /**
   * ⚑ EMIT WHATEVER GATE THIS SUITE'S RANGE CHECKS NEED TO EXIST AT ALL, once
   * per circuit body. Absent for BabyBear, whose `quotientTimesP` already emits
   * a `RangeCheck0` on every reduction. Present for Pasta, whose lane check is
   * a bare `rangeCheck3x12` and whose 12-bit lookup table kimchi therefore does
   * NOT install — a Pasta-only body compiles, analyses, passes `runAndCheck`
   * and then dies in `prove()` with "the lookup failed to find a match in the
   * table". See `PastaMmcs.assertPastaLookupTable`.
   */
  anchorLookupTable?(): void;
  /** The MMCS node compression, inputs assumed already in range. */
  compress(l: D, r: D): D;
  /** `(left, right)` for a level, where `isRight` says the CURRENT node is the
   *  right child. */
  condSwap(cur: D, sib: D, isRight: Bool): [D, D];
  /**
   * The MMCS leaf hash over a row of BabyBear lanes.
   *
   * ⚑ `lanesAlreadyChecked` distinguishes two REAL call sites, not two moods. A
   * FRI input-phase leaf is a fresh witness row whose lanes must be bounded
   * here; a commit-phase leaf is assembled from extension values the caller has
   * already bounded with `assertExtInRange`. Bounding twice is sound and moves
   * every measured row count in this arc; bounding never makes both suites'
   * packing/bound arguments claims about numbers nothing forces to be small.
   */
  sponge(row: Field[], lanesAlreadyChecked?: boolean): D;
  /**
   * ⚑ THE LEAF SPONGE AS A STREAMING MACHINE, and it is not a convenience.
   *
   * `sponge` above takes a whole row, which the SLICED walk cannot: an opened
   * row at one height of one PCS round is up to 452 base lanes, and the sponge
   * over it has to be splittable at a slice boundary with the running state
   * carried across. `RootFriSlice`'s `inBlock` segment is exactly one
   * `absorb`, and the state that crosses a cut is `stateLanes` field elements.
   *
   * ⚑ `stateLanes` AND `rate` ARE THE WALK'S SHAPE, NOT ONLY ITS PRICE. The
   * BabyBear sponge carries a 16-lane state and eats 8 lanes a permutation; the
   * Pasta MMCS carries 3 Pasta cells and eats 16. So the number of `inBlock`
   * segments, the width of the `sponge` slot, and therefore the whole slot
   * layout are functions of THIS record — which is why `RootFriWalk.WalkHash`
   * reads them from here rather than restating them.
   *
   * ⚠ NOT THE SAME GATE STREAM AS `sponge` FOR BABYBEAR, said out loud. The
   * one-shot `spongeBB` reduces the untouched capacity lanes lazily against the
   * previous permutation's bound; the streaming form must reduce all
   * `stateLanes` eagerly because the state crosses a boundary as bare lanes.
   * The digests agree; the emitted rows do not, and `poseidon2-merkle-rows`
   * pins the one-shot form.
   */
  spongeStream: SpongeStream<D>;
  /** Canonicalise for comparison against an emitted value. Identity for Pasta. */
  canonical(d: D): D;
  /** `a == b`, lane by lane, at this suite's digest width. */
  assertEq(a: D, b: D): void;
  /** True when a witnessed digest needs no range check at all — i.e. when the
   *  hash field IS the circuit's field. Pasta: true. BabyBear: false. Exposed so
   *  a measurement can report WHY a suite is cheaper rather than only that it
   *  is. */
  laneCheckIsFree: boolean;

  // -- out-of-circuit twins, for the differential ---------------------------
  compressBigInt(l: bigint[], r: bigint[]): bigint[];
  spongeBigInt(row: bigint[]): bigint[];
};

/** The transcript half. Both concrete challengers already have exactly these
 *  methods; the type is here so `DreggProofVerify` can hold one without knowing
 *  which. */
export type ChallengerLike<D extends Digestish = Digestish> = {
  observe(v: Field): void;
  observeSlice(vs: Field[]): void;
  observeDigest(d: D): void;
  observeExt(e: { limbs: Field[] }): void;
  observeConstant(c: bigint): void;
  sample(): Field;
  sampleExt(): any;
  sampleBitsAsBits(k: number): Bool[];
  assertCheckWitness(bits: number, witness: Field): void;
  /** Instrumentation only, out of circuit. */
  perms: number;
};

export type ChallengerBigIntLike = {
  observe(v: bigint): void;
  observeSlice(vs: bigint[]): void;
  observeDigest(words: bigint[]): void;
  sample(): bigint;
  sampleExt(): bigint[];
  sampleBits(bits: number): number;
  checkWitness(bits: number, witness: bigint): boolean;
  perms: number;
};

export type HashSuite<D extends Digestish = Digestish> = MerkleSuite<D> & {
  newChallenger(): ChallengerLike<D>;
  newChallengerBigInt(): ChallengerBigIntLike;
};

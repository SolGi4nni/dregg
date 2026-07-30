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

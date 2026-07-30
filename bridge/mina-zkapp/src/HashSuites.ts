import { Challenger, ChallengerBigInt } from './FriChallenger.js';
import type { ChallengerBigIntLike, ChallengerLike, HashSuite } from './HashSuiteType.js';
import { BbDigest, babyBearMerkleSuite } from './Poseidon2Merkle.js';
import { PastaChallenger, PastaChallengerBigInt } from './PastaChallenger.js';
import { PastaDigest, pastaMerkleSuite } from './PastaMmcs.js';

// ---------------------------------------------------------------------------
// THE TWO HASH SUITES, ASSEMBLED. A leaf module on purpose: it is the one place
// that imports both a Merkle half and a challenger, so no other file has to, and
// the `FriQueryStep -> FriChallenger -> FriQueryStep` cycle a combined record
// would otherwise create never forms. See `HashSuiteType.ts`.
//
// ⚑ NAME THE OBJECT EACH ONE VERIFIES, so a reader never has to infer it:
//
//   babyBearSuite  — a proof minted under `DreggStarkConfig` /
//                    `DreggRecursionConfig`. What dregg's ROOT commits with
//                    today, and what every rung before this one measured.
//                    `Poseidon2BabyBear<16>` must be EMULATED in a Pasta
//                    circuit: 2,600.5 measured rows a permutation.
//
//   pastaSuite     — a proof minted under `DreggMinaConfig`
//                    (`circuit-prove/src/dregg_mina_config.rs`). Commits with
//                    kimchi's own Poseidon over Pasta `Fp`, so o1js hashes
//                    NATIVELY: 13 measured rows a permutation. Same `Val`, same
//                    `Challenge = EF4`, same FRI knobs, same AIRs — the hash
//                    field is the only change, which is exactly why its FRI
//                    ledger reading is the ETH wrap's already-modelled entry.
// ---------------------------------------------------------------------------

export const babyBearSuite: HashSuite<BbDigest> = {
  ...babyBearMerkleSuite,
  newChallenger: () => new Challenger() as unknown as ChallengerLike<BbDigest>,
  newChallengerBigInt: () => {
    const c = new ChallengerBigInt();
    return {
      observe: (v) => c.observe(v),
      observeSlice: (vs) => c.observeSlice(vs),
      // A BabyBear digest is EIGHT lanes absorbed one at a time — no packing,
      // no length tag. The Pasta twin below is a different absorb entirely.
      observeDigest: (words) => c.observeSlice(words),
      sample: () => c.sample(),
      sampleExt: () => c.sampleExt(),
      sampleBits: (b) => c.sampleBits(b),
      checkWitness: (b, w) => c.checkWitness(b, w),
      get perms() {
        return c.perms;
      },
    } as ChallengerBigIntLike;
  },
};

export const pastaSuite: HashSuite<PastaDigest> = {
  ...pastaMerkleSuite,
  newChallenger: () => new PastaChallenger() as unknown as ChallengerLike<PastaDigest>,
  newChallengerBigInt: () => new PastaChallengerBigInt() as unknown as ChallengerBigIntLike,
};

/** Resolve a fixture's `hash` field to its suite. ⚑ REFUSES an unknown name
 *  rather than defaulting: a fixture minted under a config nobody has written a
 *  suite for must fail by NAME here, not as a digest mismatch forty thousand
 *  rows into a walk. */
export function suiteByName(name: string): HashSuite<any> {
  switch (name) {
    case 'poseidon2-babybear-w16':
      return babyBearSuite;
    case 'mina-poseidon-pasta':
      return pastaSuite;
    default:
      throw new Error(
        `no o1js hash suite for '${name}' — the fixture was minted under a config this ` +
          'verifier does not implement',
      );
  }
}

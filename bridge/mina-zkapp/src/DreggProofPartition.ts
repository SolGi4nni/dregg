import { Bool, Field, Poseidon, Provable, SelfProof, ZkProgram } from 'o1js';
import { BbDigest } from './Poseidon2Merkle.js';
import { BbExt } from './FriQueryStep.js';
import {
  ClaimValue,
  DreggProofShape,
  StarkChallenges,
  VerifyPlan,
  assertAirClosing,
  assertProofDataInRange,
  deriveStarkChallenges,
  makeDreggProofClaim,
  runQueryWalk,
  verifyPlan,
} from './DreggProofVerify.js';
import { chainStepBoundary, untaggedTerminalSeal } from './CostModel.js';

// ---------------------------------------------------------------------------
// THE PARTITION — `DreggProofVerify` split across Pickles steps, and the
// step-boundary contract that makes a sequence of steps a CHAIN.
//
// ⚑ WHY THIS EXISTS AND WHAT IT REPLACES. §3.19 put the whole of
// `p3_uni_stark::verify` in ONE Pickles step at 56,927 rows — 86.9% of the 2^16
// domain — and the same program at two queries is 80,241 rows, which the
// compiler REFUSES. So the one-step verifier is not a small version of the
// deployed one: it is the largest dregg proof that happens to fit, and every
// geometry past it needs a chain. "~573 steps" was arithmetic over a partition
// nobody had run.
//
// ⚑ THE CONTRACT IS `Dregg2/Circuit/Emit/KimchiPartition.lean`, NOT A CHOICE
// MADE HERE. `StepPublicInput` names three things and one field element:
//
//     boundary_k = Poseidon(rootCommitDigest, challengeDigest, k)
//
//   * `rootCommitDigest` binds every step to the SAME dregg proof. Without it,
//     consecutive steps verify openings against DIFFERENT proofs and the
//     aggregation still checks out.
//   * `challengeDigest` is the Fiat-Shamir state, so a later step cannot walk
//     under challenges of its own choosing. This is the one that MATTERS: the
//     query walk in step k+1 is only FRI because the index it walks is the index
//     step k DERIVED.
//   * `k` is what forbids the aggregation tree double-counting or skipping.
//
// A step re-witnesses the carried values and RE-DERIVES the digest, which is why
// a boundary costs `|carried|` re-witnessings plus a hash rather than `|carried|`
// public inputs — one full Kimchi row each (§3.2).
//
// ⚑ THE CARRIER IS MINA-POSEIDON OVER PACKED LANES, AND THAT IS A MEASURED
// DECISION. Hashing the carried BabyBear lanes with the DEPLOYED sponge
// (`spongeBB`, 2,668 rows per 8 lanes) would cost ~333 rows per lane. Eight
// 31-bit lanes pack losslessly into one 254-bit Pasta field, and Mina-Poseidon
// then absorbs two of those per permutation. The boundary does not have to be a
// BabyBear object — nothing in dregg reads it, it exists between two Kimchi
// steps — so it is not one. `partition-chain.ts` measures both and prints the
// ratio, because a carrier chosen by argument is a carrier nobody priced.
//
// ⚑ WHAT THE ROW COUNTS HERE DO NOT CONTAIN. `analyzeMethods` reports the
// method's OWN gates. Pickles' recursive-verifier overhead — the cost of
// `prev.verify()` — is in the step WRAPPER and is invisible to it, exactly the
// §3.15e hazard in reverse. So `rows(step_k)` is a LOWER bound on what a step
// spends, and the wrapper's share is measured separately by walking a padded
// program up to the compile wall with and without a proof argument.
// ---------------------------------------------------------------------------

/** A BabyBear lane is `< 2^31`; a Pasta field holds 254 bits. Eight lanes pack
 *  losslessly, and the packing is injective ONLY because every lane has been
 *  range-checked — `assertProofDataInRange` and the challenger's `sample` do
 *  that before anything reaches here. */
export const LANES_PER_FIELD = 8;
const LANE_BITS = 31n;

/** The challenge digest entering step 0: the transcript has absorbed nothing.
 *  A distinguished value rather than a hash of the empty list, because o1js's
 *  Poseidon has no empty-input case and a chain needs the base to be a CONSTANT
 *  the verifier can write down. */
export const GENESIS_CHALLENGE_DIGEST = Field(0);

/** Pack 31-bit lanes, eight to a Pasta field. Linear, so it costs a linear
 *  combination rather than a gate per lane. */
export function packLanes(lanes: Field[]): Field[] {
  const out: Field[] = [];
  for (let i = 0; i < lanes.length; i += LANES_PER_FIELD) {
    let acc = lanes[i];
    for (let j = 1; j < LANES_PER_FIELD && i + j < lanes.length; j++)
      acc = acc.add(lanes[i + j].mul(1n << (LANE_BITS * BigInt(j))));
    out.push(acc);
  }
  return out;
}

/** One field element binding a list of range-checked BabyBear lanes. */
export function digestOfLanes(lanes: Field[], pack: boolean): Field {
  return Poseidon.hash(pack ? packLanes(lanes) : lanes);
}

/** `StepPublicInput` — the whole public input of a work step, on the wire.
 *  `stepIndex` is a `Field` rather than a build-time number wherever the step
 *  index is CARRIED: a uniform walk circuit is invoked at every position, so its
 *  own index cannot be baked in — it is forced by the chain instead (see
 *  `makeChainedProofVerify`). */
/** ⚑ RE-EXPORTED, NOT RE-DEFINED — see `CostModel.chainStepBoundary`. This and
 *  `RootAirChain.stepBoundary` were two identical bodies under one name. */
export const stepBoundary = chainStepBoundary;

/** The chain's CLOSING boundary — the one field a verifier checks against the
 *  terminal proof. Same three-slot shape as the entry, with the challenge slot
 *  empty and the index at `nSteps`: "the chain over THIS proof closed after
 *  exactly this many steps". Both ends of the chain are therefore computable
 *  from the dregg proof alone, and neither needs the transcript the verifier
 *  delegated.
 *
 *  ⚑ NAMED `partition…`: this is the THREE-field UNTAGGED seal, and the AIR/FRI
 *  chain's `airTerminalSeal` is four-field and domain-tagged. Both were called
 *  `terminalSeal` and differed only by arity, which is not a mechanism. */
export const partitionTerminalSeal = untaggedTerminalSeal;

/**
 * The lanes `rootCommitDigest` covers.
 *
 * ⚑ WIDER THAN ITS NAME, DELIBERATELY. The Lean calls it the digest of the
 * proof's commitments; here it covers the whole proof OBJECT the steps share —
 * commitments, final polynomial, public values, every claimed out-of-domain
 * evaluation and the query PoW witness. The opened evaluations have to be in
 * it: the DEEP quotient in a later step reads them, and a digest that did not
 * cover them would let a step splice openings from another proof while every
 * commitment matched. The per-query MMCS rows and paths are NOT here — each
 * belongs to exactly one step and never crosses a boundary.
 */
export function rootCommitLanes(
  claim: ClaimValue,
  openedTrace: BbExt[],
  openedQuotient: BbExt[],
  queryPowWitness: Field,
): Field[] {
  const lanes: Field[] = [];
  for (const d of claim.inputCommits) lanes.push(...d.limbs);
  for (const d of claim.commitPhaseCommits) lanes.push(...d.limbs);
  for (const e of claim.finalPoly) lanes.push(...e.limbs);
  lanes.push(...claim.publicValues);
  for (const e of openedTrace) lanes.push(...e.limbs);
  for (const e of openedQuotient) lanes.push(...e.limbs);
  lanes.push(queryPowWitness);
  return lanes;
}

/** The lanes `challengeDigest` covers: the whole Fiat-Shamir output of step 0.
 *  Every query's index is in here even though a step walks only its own — the
 *  carried state is the transcript, not a step's slice of it. */
export function challengeLanes(plan: VerifyPlan, ch: StarkChallenges): Field[] {
  const lanes: Field[] = [...ch.alphaStark.limbs, ...ch.zeta.limbs, ...ch.friAlpha.limbs];
  for (const b of ch.betas) lanes.push(...b.limbs);
  const k = plan.sh.knobs.indexBits;
  for (const qb of ch.queryBits) {
    let acc = Field(0);
    for (let i = 0; i < k; i++) acc = acc.add(qb[i].toField().mul(1n << BigInt(i)));
    lanes.push(acc);
  }
  return lanes;
}

/** How many lanes cross a boundary at a given shape — the number the deployed
 *  projection is a function of. Out of circuit; no witness needed. */
export function carriedLaneCount(sh: DreggProofShape): { root: number; challenge: number } {
  const plan = verifyPlan(sh);
  const { knobs, air } = sh;
  return {
    root:
      plan.nBatches * 8 +
      knobs.layers * 8 +
      knobs.finalPolyLen * 4 +
      Math.max(air.numPublicValues, 1) +
      plan.nOpenedTrace * 4 +
      plan.nQuotientVals * 4 +
      1,
    challenge: 4 + 4 + 4 + knobs.layers * 4 + knobs.numQueries,
  };
}

// ===========================================================================
// The chain.
//
// ⚑ ONE WALK CIRCUIT, INVOKED N TIMES — NOT N CIRCUITS. The first version of
// this built one ZkProgram per step. It works at three steps and it does not
// scale: a verifier would need one VK per step, "573 steps" would mean 573
// compiles, and — measured — a node process that has compiled four step circuits
// HANGS at the first `prove` (kimchi's wasm heap is 32-bit; the worker dies and
// the promise never settles). So the walk is a SINGLE program with TWO methods,
// `first` (its predecessor is the transcript step) and `step` (its predecessor is
// itself), and a chain of any length is that one VK invoked repeatedly. Three
// step circuits is what fits; that is not a design preference, it is the wall.
//
// ⚑ AND THE STEP INDEX IS THEN A WITNESS, WHICH IS ONLY SAFE BECAUSE THE CHAIN
// FORCES IT. A uniform circuit cannot bake in its own position, so `k` is a
// private input — and a private input is a value the prover chooses. It is
// pinned by three things together, none of which is sufficient alone:
//
//   * `first` uses the CONSTANT k = 1;
//   * `step` checks `Poseidon(rcd, cd, k) == publicInput` and
//     `predecessor.publicOutput == publicInput`, while the predecessor emitted
//     `Poseidon(rcd, cd, k_prev + 1)` — so `k = k_prev + 1` by collision
//     resistance, inductively from 1;
//   * the terminal seal carries `k + 1`, and the verifier compares it against
//     `nSteps`, so the chain cannot stop early.
//
// ⚑ AND `isLast` IS A WITNESS FOR THE SAME REASON AND WITH THE SAME ANSWER. One
// circuit cannot know whether it is the last step, so the step emits a seal or a
// boundary on a witnessed bit. A prover that sets it early emits a seal at ITS
// index, and the verifier is checking the seal at `nSteps`; a prover that never
// sets it emits a boundary, which is not a seal at all. Neither passes. That is
// why the seal carries the index rather than being a bare `rootCommitDigest` —
// a bare one would let a one-step chain close.
//
// Step `k` walks query `k-1`, selected from the carried index set by a
// multiplexer that also asserts `1 <= k <= num_queries`. Together those are
// `KimchiPartition.chunks_concat` as an IN-CIRCUIT invariant rather than a Lean
// theorem about a list: every query is walked exactly once, none twice, none
// skipped, and a chain that dropped one cannot produce the terminal seal.
// ===========================================================================

export type ChainOpts = {
  /** Pack lanes before hashing. False measures what the naive carrier costs. */
  pack?: boolean;
  /** ⚑ THE CONTROL, AND IT IS NEVER PROVED AS IF IT VERIFIED ANYTHING. When
   *  false the walk still verifies its predecessor's PROOF but does not check
   *  the carried digest — so it accepts a spliced witness, which is what makes a
   *  refusal by the real step attributable to the binding and not to the walk. */
  bindCarry?: boolean;
};

/**
 * Select query `k-1`'s index bits out of the carried set, and assert
 * `1 <= k <= num_queries` while doing it.
 *
 * The assertion is not decoration: without it a prover could witness `k` outside
 * the range, the one-hot would be all-false, the multiplexer would silently
 * return query 0's bits, and the step would walk a query it was not assigned.
 */
export function selectQueryBits(
  all: Bool[][],
  k: Field,
  numQueries: number,
  indexBits: number,
): Bool[] {
  const isK = Array.from({ length: numQueries }, (_, q) => k.equals(Field(q + 1)));
  let cnt = Field(0);
  for (const b of isK) cnt = cnt.add(b.toField());
  cnt.assertEquals(Field(1));
  const out: Bool[] = [];
  for (let b = 0; b < indexBits; b++) {
    let cur = all[0][b];
    for (let q = 1; q < numQueries; q++) cur = Provable.if(isK[q], all[q][b], cur);
    out.push(cur);
  }
  return out;
}

export function makeChainedProofVerify(sh: DreggProofShape, opts: ChainOpts = {}) {
  const pack = opts.pack ?? true;
  const bind = opts.bindCarry ?? true;

  // Step 0 DERIVES the transcript; every walk step CARRIES it. That asymmetry is
  // the partition: a walk step that re-derived would be paying for step 0 again,
  // and one that witnessed WITHOUT the carried digest would not be verifying FRI.
  const shHead: DreggProofShape = { ...sh, deriveChallenges: true };
  const shWalk: DreggProofShape = { ...sh, deriveChallenges: false, constraints: undefined };
  const planHead = verifyPlan(shHead);
  const planWalk = verifyPlan(shWalk);
  const Claim = makeDreggProofClaim(sh);
  const { knobs } = sh;
  const { layers, numQueries, indexBits: nIndexBits } = knobs;
  const { nOpenedTrace, nQuotientVals, totalRow, maxInputDepth, maxCommitDepth, nBatches } =
    planHead;
  const tag =
    `w${sh.air.width}-q${numQueries}-l${layers}-h${sh.logGlobalMaxHeight}` +
    (pack ? '' : '-unpacked');

  /** The number of Pickles steps this chain is: one transcript step plus one
   *  step per query. The terminal seal carries it, so it is not a convention. */
  const nSteps = numQueries + 1;

  const proofInputs = [
    Claim,
    Provable.Array(BbExt, nOpenedTrace),
    Provable.Array(BbExt, nQuotientVals),
    Field, //                                                query_pow_witness
  ];

  const step0 = ZkProgram({
    name: `dregg-verify-step0-transcript-air-${tag}`,
    /** ONE field element: `boundary_0 = Poseidon(rootCommitDigest, 0, 0)`. */
    publicInput: Field,
    publicOutput: Field,
    methods: {
      transcriptAndAir: {
        privateInputs: proofInputs as any,
        async method(
          bIn: Field,
          claim: ClaimValue,
          openedTrace: BbExt[],
          openedQuotient: BbExt[],
          queryPowWitness: Field,
        ) {
          assertProofDataInRange(claim, openedTrace, openedQuotient);
          const rcd = digestOfLanes(
            rootCommitLanes(claim, openedTrace, openedQuotient, queryPowWitness),
            pack,
          );
          // The chain's ENTRY, and one of the two boundaries a verifier can
          // write down without running the transcript itself.
          stepBoundary(rcd, GENESIS_CHALLENGE_DIGEST, 0).assertEquals(bIn);

          const ch = deriveStarkChallenges(
            planHead,
            claim,
            openedTrace,
            openedQuotient,
            queryPowWitness,
          );
          assertAirClosing(planHead, claim, openedTrace, openedQuotient, ch);

          const cd = digestOfLanes(challengeLanes(planHead, ch), pack);
          return { publicOutput: stepBoundary(rcd, cd, 1) };
        },
      },
    },
  });

  class Step0Proof extends ZkProgram.Proof(step0) {}

  /** One walk step's carried + own-query witness, in method-argument order. */
  const walkTail = [
    ...proofInputs,
    BbExt, //                                              carried alpha_stark
    BbExt, //                                              carried zeta
    BbExt, //                                              carried fri alpha
    Provable.Array(BbExt, layers), //                      carried betas
    Provable.Array(Provable.Array(Bool, nIndexBits), numQueries), // carried indices
    Provable.Array(Provable.Array(Field, totalRow), 1), //           this step's rows
    Provable.Array(Provable.Array(Provable.Array(BbDigest, maxInputDepth), nBatches), 1),
    Provable.Array(Provable.Array(BbExt, layers), 1),
    Provable.Array(Provable.Array(Provable.Array(BbDigest, maxCommitDepth), layers), 1),
  ];

  function makeWalk(bindThis: boolean) {
    /** The one body all three methods share — so `first`, `next` and `last`
     *  cannot drift into three verifiers that agree today. */
    /** The one body both methods share — so `first` and `step` cannot drift
     *  into two verifiers that agree today. */
    const body = (bIn: Field, prev: any, k: Field, isLast: Bool, isFirst: boolean, a: any[]) => {
      const [
        claim,
        openedTrace,
        openedQuotient,
        queryPowWitness,
        alphaStark,
        zeta,
        friAlpha,
        betas,
        queryBits,
        rows,
        inputPaths,
        siblings,
        commitPaths,
      ] = a;
      prev.verify();

      assertProofDataInRange(claim, openedTrace, openedQuotient);
      const ch = deriveStarkChallenges(
        planWalk,
        claim,
        openedTrace,
        openedQuotient,
        queryPowWitness,
        { alphaStark, zeta, friAlpha, betas, queryBits },
      );

      const rcd = digestOfLanes(
        rootCommitLanes(claim, openedTrace, openedQuotient, queryPowWitness),
        pack,
      );
      const cd = digestOfLanes(challengeLanes(planWalk, ch), pack);

      if (bindThis) {
        // (i) the boundary this step ENTERS is the one its own re-witnessed
        //     values imply, AT ITS OWN INDEX — so a step cannot be replayed at
        //     another position in the chain;
        stepBoundary(rcd, cd, k).assertEquals(bIn);
        // (ii) and it is the boundary the predecessor EMITTED. Without this the
        //     step would be verifying a self-consistent walk under challenges it
        //     chose, which is not FRI.
        prev.publicOutput.assertEquals(bIn);
        // (iii) the head's entry is anchored to the SAME proof. Only `first` can
        //     do this — its predecessor's entry IS the chain's.
        if (isFirst)
          prev.publicInput.assertEquals(stepBoundary(rcd, GENESIS_CHALLENGE_DIGEST, 0));
      }

      // Step k walks query k-1, chosen from the CARRIED index set.
      const bits = selectQueryBits(ch.queryBits, k, numQueries, nIndexBits);
      runQueryWalk(
        planWalk,
        claim,
        openedTrace,
        openedQuotient,
        { ...ch, queryBits: [bits] },
        rows,
        inputPaths,
        siblings,
        commitPaths,
        [0],
      );

      const kOut = k.add(1);
      return {
        publicOutput: Provable.if(
          isLast,
          partitionTerminalSeal(rcd, kOut),
          stepBoundary(rcd, cd, kOut),
        ),
      };
    };

    return ZkProgram({
      name: `dregg-verify-walk-${tag}${bindThis ? '' : '-UNBOUND'}`,
      publicInput: Field,
      publicOutput: Field,
      methods: {
        /** k = 1 — the CONSTANT that starts the induction. */
        first: {
          privateInputs: [Step0Proof, Bool, ...walkTail] as any,
          async method(bIn: Field, prev: Step0Proof, isLast: Bool, ...a: any[]) {
            return body(bIn, prev, Field(1), isLast, true, a);
          },
        },
        /** k > 1, forced by the predecessor's emitted boundary. */
        step: {
          privateInputs: [SelfProof, Field, Bool, ...walkTail] as any,
          async method(
            bIn: Field,
            prev: SelfProof<Field, Field>,
            k: Field,
            isLast: Bool,
            ...a: any[]
          ) {
            return body(bIn, prev, k, isLast, false, a);
          },
        },
      },
    });
  }

  const walk = makeWalk(bind);

  return {
    step0,
    walk,
    Step0Proof,
    Claim,
    planHead,
    planWalk,
    pack,
    bind,
    nSteps,
    numQueries,
    /** ⚑ THE CONTROL, BUILT AGAINST THE SAME PREDECESSOR TYPE. The walk with the
     *  three boundary assertions removed and NOTHING else changed. It exists to
     *  be shown ACCEPTING a splice the real walk refuses. */
    unboundWalk: () => makeWalk(false),
  };
}

// ===========================================================================
// The out-of-circuit side of the contract.
//
// ⚑ THE SAME FUNCTIONS, ON CONSTANTS. `digestOfLanes`, `packLanes`,
// `stepBoundary` and `partitionTerminalSeal` are `Field` arithmetic and evaluate outside
// a circuit, so the harness and the circuit compute the boundary in ONE place. A
// second implementation that "agrees today" is the drift this repo has paid for.
// ===========================================================================

/** The boundary a verifier can write down from a dregg proof: `boundary_0`. */
export function entryBoundaryOf(
  claim: ClaimValue,
  openedTrace: BbExt[],
  openedQuotient: BbExt[],
  queryPowWitness: Field,
  pack: boolean,
): { rcd: Field; boundary: Field } {
  const rcd = digestOfLanes(
    rootCommitLanes(claim, openedTrace, openedQuotient, queryPowWitness),
    pack,
  );
  return { rcd, boundary: stepBoundary(rcd, GENESIS_CHALLENGE_DIGEST, 0) };
}

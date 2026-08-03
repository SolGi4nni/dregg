import { Bool, Field, Provable, SelfProof, ZkProgram } from 'o1js';
import { BbExt, EXT_D } from './FriQueryStep.js';
import {
  assertProofDataInRange,
  deriveStarkChallenges,
  makeDreggProofClaim,
  runQueryWalk,
  verifyPlan,
  type ClaimValue,
  type DreggProofShape,
  type StarkChallenges,
} from './DreggProofVerify.js';
import {
  GENESIS_CHALLENGE_DIGEST,
  challengeLanes,
  digestOfLanes,
  partitionTerminalSeal,
  rootCommitLanes,
  selectQueryBits,
  stepBoundary,
} from './DreggProofPartition.js';
import {
  ChainClaim,
  ClaimedBoundary,
  NUM_CHAIN_CLAIMS,
  assertClaimCarried,
  claimOfLanes,
} from './RootClaim.js';
import { canonicalLane } from './Poseidon2BabyBearW16.js';

// ---------------------------------------------------------------------------
// THE FULL 38-BATCH SHRINK PARTITION — o1js verifies EVERY query of dregg's
// native-Pasta shrink terminal, SEALS the G→H ChainClaim to the authenticated
// opened trace, and closes into a terminal a head gate consumes.
//
// ⚑ WHY A PARTITION AT ALL. `MinaShrinkVerify` proves ONE query batch: at 38
// queries the circuit is ~5.8M gates and o1js's `compile()` overflows the napi
// string. A batch-STARK verifier is therefore intrinsically a Pickles chain —
// exactly what the deployed root verifier is. This module is that chain for the
// shrink terminal: `step0` establishes the carried transcript + seals the claim,
// then ONE `walk` program (a SelfProof, two methods `first`/`step`) verifies ONE
// query per step, invoked 38 times. TWO VKs total (step0, walk).
//
// ⚑ THE TRANSCRIPT IS CARRIED, NOT DERIVED — and that is forced, not a shortcut.
// The shrink is a 6-instance batch STARK; `DreggProofVerify.deriveStarkChallenges`
// is a single-instance uni-stark model (`air.numPublicValues = 0` here), so it
// CANNOT faithfully re-derive the 6-instance preamble. `MinaShrinkVerify` carries
// the challenges for exactly this reason, and so does this partition: step0 and
// every walk step witness (and range-check) the SAME challenge set, and the
// boundary's `challengeDigest` forces every step to walk under it. The Fiat-Shamir
// derivation is discharged Rust-side (the fixture self-checks against the real p3
// Mina `TwoAdicFriPcs::verify`); in o1js it rides as the §3.14 carried residual,
// the same one the deployed root path carries.
//
// ⚑ THE CLAIM IS SEALED TO THE AUTHENTICATED TRACE — NOT A FREE WITNESS. The
// exposed `expose_claim` instance (`claimInstance`) is a degree-0 (constant)
// trace, so its opened value at ζ EQUALS its trace cell = the claim lane. Those
// opened trace values feed EVERY query's DEEP quotient, which folds to dregg's
// REAL emitted commit-phase commitments and final polynomial — bend one and the
// fold diverges and every walk step refuses. So `readSealedClaim` reads the 25
// chain-claim lanes straight out of `openedTrace` (base limb of column `4·i` in
// the claim matrix), range-checks them, and packs the `ChainClaim`. There is no
// separate claim witness to forge: the claim a Mina-side verifier reads is the
// one the FRI walk authenticated against dregg's own commitments.
//
// ⚑ WHAT IS AND IS NOT BOUND, at current resolution. BOUND in-circuit: the opened
// values (trace + quotient + the claim lanes among them) against dregg's emitted
// Pasta commitments (input-batch + commit-phase Merkle openings, DEEP fold to the
// emitted final poly), across ALL 38 queries. CARRIED (Rust-side, not re-derived
// in o1js): the Fiat-Shamir transcript that fixes the challenges/query indices,
// and the AIR closing equalities (`constraints` absent — PCS floor). The FRI/STARK
// low-degree soundness floor is as undischarged here as everywhere in this tree.
// ---------------------------------------------------------------------------

const LANE_MAX = (1n << 31n) - 1n;

/** The flat `openedTrace` offset of round-0 matrix `claimInstance`'s point-0
 *  values — the sum of every earlier round-0 matrix's `numPoints·numCols`. */
export function claimTraceOffset(sh: DreggProofShape, claimInstance: number): number {
  const round0 = sh.batches[0].matrices;
  if (claimInstance < 0 || claimInstance >= round0.length)
    throw new Error(
      `claimInstance ${claimInstance} is outside round 0's ${round0.length} matrices`,
    );
  let off = 0;
  for (let m = 0; m < claimInstance; m++) off += round0[m].numPoints * round0[m].numCols;
  return off;
}

/**
 * Read the 25 chain-claim lanes out of the AUTHENTICATED opened trace and pack
 * the `ChainClaim`. Lane `i` is the base limb of the claim matrix's column
 * `EXT_D·i`; the other three limbs are zero because a public value is a base
 * element, and the base is range-checked `< 2^31` so `claimOfLanes`'s octet
 * packing is injective.
 */
export function readSealedClaim(
  sh: DreggProofShape,
  claimInstance: number,
  openedTrace: BbExt[],
): ChainClaim {
  const off = claimTraceOffset(sh, claimInstance);
  const lanes: Field[] = [];
  for (let i = 0; i < NUM_CHAIN_CLAIMS; i++) {
    const e = openedTrace[off + EXT_D * i];
    if (e === undefined)
      throw new Error(
        `claim lane ${i} wants openedTrace[${off + EXT_D * i}] but only ${openedTrace.length} ` +
          'opened trace values exist — the claim matrix offset is wrong',
      );
    //  A public value is a BASE element: extension limbs 1..3 are zero.
    e.limbs[1].assertEquals(Field(0));
    e.limbs[2].assertEquals(Field(0));
    e.limbs[3].assertEquals(Field(0));
    lanes.push(canonicalLane(e.limbs[0], LANE_MAX));
  }
  return claimOfLanes(lanes);
}

/**
 * Build the two-program shrink partition at a shape + claim instance.
 *
 * `step0`  : publicInput `boundary_0 = stepBoundary(rcd, GENESIS, 0)`,
 *            publicOutput `ClaimedBoundary{ stepBoundary(rcd, cd, 1), claim }`.
 * `walk`   : one SelfProof, methods `first`/`step`; each walks ONE query and
 *            carries the claim; the last emits the terminal seal.
 */
export function makeMinaShrinkPartition(sh: DreggProofShape, claimInstance: number) {
  //  Both step0 and the walk CARRY the transcript (derive is unfaithful for a
  //  6-instance batch STARK — see the header). `constraints` is already absent.
  const shCarry: DreggProofShape = { ...sh, deriveChallenges: false, constraints: undefined };
  const plan = verifyPlan(shCarry);
  if (plan.derive)
    throw new Error('the shrink partition must CARRY the transcript; this shape says derive');
  const Claim = makeDreggProofClaim(shCarry);
  const { knobs } = shCarry;
  const { layers, numQueries, indexBits: nIndexBits } = knobs;
  const { nOpenedTrace, nQuotientVals, totalRow, maxInputDepth, maxCommitDepth, nBatches } = plan;

  /** One transcript step plus one step per query; the terminal seal carries it. */
  const nSteps = numQueries + 1;
  const Digest = plan.suite.Digest;

  //  Each step re-witnesses + range-checks all ~1,786 opened extension values and
  //  walks (or, for step0, seals) — a ~150K-row body, the same 2^18 geometry that
  //  forced `MinaShrinkVerify` past the 2^13 wrap / 2^16 kimchi defaults. step0
  //  (no recursion, no query walk) is the smaller of the two, so it needs a
  //  smaller wrap domain than the walk. Both env-tunable per program.
  const wrapS0 = Number(process.env.MINA_STEP0_WRAP_DOMAIN ?? 0) as 0 | 1 | 2;
  const chunksS0 = Number(process.env.MINA_STEP0_NUM_CHUNKS ?? 1);
  const wrapW = Number(process.env.MINA_WALK_WRAP_DOMAIN ?? 2) as 0 | 1 | 2;
  const chunksW = Number(process.env.MINA_WALK_NUM_CHUNKS ?? 4);

  /** The proof-global witness every step re-witnesses (shared, so `rcd` and the
   *  claim agree across the chain). */
  const proofGlobal = [
    Claim,
    Provable.Array(BbExt, nOpenedTrace),
    Provable.Array(BbExt, nQuotientVals),
    Field, //                                                 query_pow_witness
    BbExt, //                                                 carried alpha_stark
    BbExt, //                                                 carried zeta
    BbExt, //                                                 carried fri alpha
    Provable.Array(BbExt, layers), //                         carried betas
    Provable.Array(Provable.Array(Bool, nIndexBits), numQueries), // carried indices (ALL)
  ];

  /** step0 witnesses only the proof-global set — it walks no query. */
  const step0Inputs = proofGlobal;

  /** A walk step adds ONE query's Merkle-opening witness. */
  const walkTail = [
    ...proofGlobal,
    Provable.Array(Provable.Array(Field, totalRow), 1), //                    this query's rows
    Provable.Array(Provable.Array(Provable.Array(Digest, maxInputDepth), nBatches), 1),
    Provable.Array(Provable.Array(BbExt, layers), 1),
    Provable.Array(Provable.Array(Provable.Array(Digest, maxCommitDepth), layers), 1),
  ];

  /** Re-derive the carried challenge set (range-checked) and the two digests
   *  from a step's re-witnessed proof-global values. */
  const digestsOf = (
    claim: ClaimValue,
    openedTrace: BbExt[],
    openedQuotient: BbExt[],
    queryPowWitness: Field,
    alphaStark: BbExt,
    zeta: BbExt,
    friAlpha: BbExt,
    betas: BbExt[],
    queryBits: Bool[][],
  ): { ch: StarkChallenges; rcd: Field; cd: Field } => {
    assertProofDataInRange(claim, openedTrace, openedQuotient);
    const ch = deriveStarkChallenges(plan, claim, openedTrace, openedQuotient, queryPowWitness, {
      alphaStark,
      zeta,
      friAlpha,
      betas,
      queryBits,
    });
    const rcd = digestOfLanes(
      rootCommitLanes(claim, openedTrace, openedQuotient, queryPowWitness),
      true,
    );
    const cd = digestOfLanes(challengeLanes(plan, ch), true);
    return { ch, rcd, cd };
  };

  const step0 = ZkProgram({
    name: `mina-shrink-step0-q${numQueries}-l${layers}-h${sh.logGlobalMaxHeight}`,
    publicInput: Field,
    publicOutput: ClaimedBoundary,
    overrideWrapDomain: wrapS0,
    numChunks: chunksS0,
    methods: {
      transcript: {
        privateInputs: step0Inputs as any,
        async method(
          bIn: Field,
          claim: ClaimValue,
          openedTrace: BbExt[],
          openedQuotient: BbExt[],
          queryPowWitness: Field,
          alphaStark: BbExt,
          zeta: BbExt,
          friAlpha: BbExt,
          betas: BbExt[],
          queryBits: Bool[][],
        ) {
          const stage = process.env.MINA_S0_STAGE ?? 'full';
          const zeroClaim = claimOfLanes(Array.from({ length: NUM_CHAIN_CLAIMS }, () => Field(0)));
          if (stage === 'apri') {
            assertProofDataInRange(claim, openedTrace, openedQuotient);
            return { publicOutput: new ClaimedBoundary({ boundary: bIn, claim: zeroClaim }) };
          }
          if (stage === 'seal') {
            const claimS = readSealedClaim(shCarry, claimInstance, openedTrace);
            return { publicOutput: new ClaimedBoundary({ boundary: bIn, claim: claimS }) };
          }
          if (stage === 'range') {
            assertProofDataInRange(claim, openedTrace, openedQuotient);
            const claimR = readSealedClaim(shCarry, claimInstance, openedTrace);
            return { publicOutput: new ClaimedBoundary({ boundary: bIn, claim: claimR }) };
          }
          const { rcd, cd } = digestsOf(
            claim,
            openedTrace,
            openedQuotient,
            queryPowWitness,
            alphaStark,
            zeta,
            friAlpha,
            betas,
            queryBits,
          );
          if (stage === 'digests') {
            const claimD = readSealedClaim(shCarry, claimInstance, openedTrace);
            return { publicOutput: new ClaimedBoundary({ boundary: stepBoundary(rcd, cd, 1), claim: claimD }) };
          }
          //  The chain's ENTRY, computable from the proof alone.
          stepBoundary(rcd, GENESIS_CHALLENGE_DIGEST, 0).assertEquals(bIn);
          //  SEAL: the claim is read from the (later-authenticated) opened trace,
          //  the same `openedTrace` `rcd` covers, so the walk cannot swap it.
          const claimOut = readSealedClaim(shCarry, claimInstance, openedTrace);
          return {
            publicOutput: new ClaimedBoundary({ boundary: stepBoundary(rcd, cd, 1), claim: claimOut }),
          };
        },
      },
    },
  });

  class Step0Proof extends ZkProgram.Proof(step0) {}

  function makeWalk(bindThis: boolean) {
    const body = (
      bIn: Field,
      prev: { verify: () => void; publicInput: Field; publicOutput: ClaimedBoundary },
      k: Field,
      isLast: Bool,
      isFirst: boolean,
      a: any[],
    ) => {
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

      const { ch, rcd, cd } = digestsOf(
        claim,
        openedTrace,
        openedQuotient,
        queryPowWitness,
        alphaStark,
        zeta,
        friAlpha,
        betas,
        queryBits,
      );

      if (bindThis) {
        //  (i) the boundary this step enters is its own re-witnessed values, at
        //      its own index — a step cannot be replayed at another position.
        stepBoundary(rcd, cd, k).assertEquals(bIn);
        //  (ii) and it is the boundary the predecessor emitted.
        prev.publicOutput.boundary.assertEquals(bIn);
        //  (iii) `first` anchors the predecessor's ENTRY to the SAME proof.
        if (isFirst)
          prev.publicInput.assertEquals(stepBoundary(rcd, GENESIS_CHALLENGE_DIGEST, 0));
      }

      //  CARRY: re-seal the claim from THIS step's authenticated opened trace and
      //  require it to equal the predecessor's. `rcd` binds `openedTrace` across
      //  the chain, so both are the same authenticated values.
      const claimHere = readSealedClaim(shCarry, claimInstance, openedTrace);
      if (bindThis) assertClaimCarried(prev.publicOutput.claim, claimHere);

      //  Step k walks query k-1, its bits selected from the carried GLOBAL set
      //  and re-indexed to local position 0.
      const bits = selectQueryBits(ch.queryBits, k, numQueries, nIndexBits);
      runQueryWalk(
        plan,
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
      const boundary = Provable.if(
        isLast,
        partitionTerminalSeal(rcd, kOut),
        stepBoundary(rcd, cd, kOut),
      );
      return { publicOutput: new ClaimedBoundary({ boundary, claim: claimHere }) };
    };

    return ZkProgram({
      name: `mina-shrink-walk-q${numQueries}-l${layers}-h${sh.logGlobalMaxHeight}${bindThis ? '' : '-UNBOUND'}`,
      publicInput: Field,
      publicOutput: ClaimedBoundary,
      overrideWrapDomain: wrapW,
      numChunks: chunksW,
      methods: {
        /** k = 1 — the constant that starts the induction. */
        first: {
          privateInputs: [Step0Proof, Bool, ...walkTail] as any,
          async method(bIn: Field, prev: Step0Proof, isLast: Bool, ...a: any[]) {
            return body(bIn, prev as any, Field(1), isLast, true, a);
          },
        },
        /** k > 1, forced by the predecessor's emitted boundary. */
        step: {
          privateInputs: [SelfProof, Field, Bool, ...walkTail] as any,
          async method(
            bIn: Field,
            prev: SelfProof<Field, ClaimedBoundary>,
            k: Field,
            isLast: Bool,
            ...a: any[]
          ) {
            return body(bIn, prev as any, k, isLast, false, a);
          },
        },
      },
    });
  }

  const walk = makeWalk(true);

  return {
    step0,
    walk,
    Step0Proof,
    Claim,
    plan,
    nSteps,
    numQueries,
    claimInstance,
    /** The control with the three boundary + claim-carry assertions removed —
     *  exists to be shown ACCEPTING a splice the real walk refuses. */
    unboundWalk: () => makeWalk(false),
  };
}

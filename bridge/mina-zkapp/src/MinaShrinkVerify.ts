import { Bool, Field, Provable, ZkProgram } from 'o1js';
import {
  BbExt,
} from './FriQueryStep.js';
import {
  assertAirClosing,
  assertProofDataInRange,
  deriveStarkChallenges,
  makeDreggProofClaim,
  runQueryWalk,
  verifyPlan,
  type DreggProofShape,
} from './DreggProofVerify.js';
import type { Digestish } from './HashSuiteType.js';
import { rootShapeOf, rootValues, rootClaim, rootWitness, type RootValues } from './RootConsume.js';
import { pastaSuite } from './HashSuites.js';
import { ChainClaim, claimOfLanes, NUM_CHAIN_CLAIMS } from './RootClaim.js';
import { assertLaneLt2p31 } from './Poseidon2BabyBearW16.js';

// ---------------------------------------------------------------------------
// THE MISSING PIECE, BUILT: an o1js Kimchi verifier of dregg's NATIVE-PASTA
// SHRINK TERMINAL — `shrink_apex_to_outer(apex, DreggMinaConfig)`, a single
// 2^15 batch-STARK whose Merkle roots are single native Pasta `Fp` elements and
// whose transcript is the Mina-Poseidon `MultiField32Challenger`.
//
// ⚑ WHY THIS BINDS AND THE 199-INSTANCE PASTA CHAIN DOES NOT. That chain is fed
// `rehashRealRootFri` — the MMCS digests are RECOMPUTED from the openings under
// Pasta, so `assertEq(recomputed, commit)` is `assertEq(f(openings), f(openings))`,
// a tautology that binds to nothing (`RootConsume.ts:389-393`). This verifier is
// fed the REAL commitments dregg emitted natively over Pasta (`rehashed:false`):
// `verifyInputBatches` recomputes each query's Merkle root from the opened rows
// with `Poseidon.hash` and `assertEq`s it against dregg's OWN emitted root
// (`DreggProofVerify.ts:735`). Tamper one opened row and the recomputed root
// diverges from the emitted one → REFUSED. That is a commitment binding, not a
// re-mint.
//
// ⚑ REUSE, NOT REINVENTION. The shrink terminal is a 5-instance / 4-PCS-round
// batch STARK — the SAME family `RootConsume` already reads for the 7-instance
// root. So the shape/witness come straight from `rootShapeOf` / `rootValues` /
// `rootWitness` (with `pastaSuite`, real Pasta digests), and the FRI walk /
// DEEP quotient / input-batch openings are `DreggProofVerify`'s, unchanged. What
// this module adds is (a) the pasta-real values reader and (b) exposing the
// apex's G→H `ChainClaim` (genesis→final root, num_turns, chain digest) as the
// program's PUBLIC OUTPUT, so a head gate can pin it.
//
// ⚑ SCOPE, said plainly (the `RootConsume.ROOT_CHALLENGE_STATUS` resolution).
// This is a PCS-floor verifier at CARRIED challenges: it authenticates the
// opened values against dregg's emitted Pasta commitments (input-batch + FRI
// commit-phase Merkle openings, the DEEP-quotient fold reaching the emitted
// final poly), on the universal FRI/MMCS floor. It does NOT re-evaluate the
// apex-verifier AIR closing equalities (`constraints` absent) — that stays the
// STARK layer's job — and the batch-STARK preamble transcript is CARRIED, not
// re-derived (the §3.14 residual the deployed root path also carries). The
// claim's binding to the committed trace is the shrink proof's own
// `ExposeClaimAir` quotient identity (Rust side); here the claim rides as a
// transcript-observed public value of a commitment-bound proof. What is DERIVED
// and what is CARRIED is exactly what it is for the root.
// ---------------------------------------------------------------------------

/** The pasta-native, NOT-rehashed values reader — `rootValues` with the honest
 *  hash label. dregg emitted these Pasta digests natively; nothing is
 *  recomputed, which is the whole point (contrast `rehashRealRootFri`). */
export function shrinkValues(real: any): RootValues {
  const v = rootValues(real);
  v.hash = { name: 'mina-poseidon-pasta', rehashed: false };
  return v;
}

/** The shape of a native-Pasta shrink terminal — `rootShapeOf` at `pastaSuite`,
 *  no constraints (PCS floor). */
export function shrinkShapeOf(real: any): DreggProofShape {
  return rootShapeOf(real, pastaSuite);
}

/** The 25 claim lanes (`[genesis8, final8, count, digest8]`) the fixture carries
 *  in its `expose_claim` table, as circuit Fields. */
export function claimLaneFields(real: any): Field[] {
  const lanes: number[] = (real.claimLanes as number[]).slice(0, NUM_CHAIN_CLAIMS);
  if (lanes.length !== NUM_CHAIN_CLAIMS)
    throw new Error(`fixture carries ${lanes.length} claim lanes, want ${NUM_CHAIN_CLAIMS}`);
  return lanes.map((x) => Field(BigInt(x)));
}

/**
 * Build the `ZkProgram` that verifies ONE native-Pasta shrink terminal and
 * exposes its `ChainClaim` (G→H) as public output.
 *
 * `publicInput` is the proof identity `DreggProofClaim` — its `inputCommits` are
 * dregg's REAL emitted Pasta commitments, so a head gate pins them (which apex /
 * which root); `publicOutput` is the `ChainClaim` the verified proof attests.
 */
export function makeMinaShrinkVerifyProgram(sh: DreggProofShape) {
  const plan = verifyPlan(sh);
  const { air, logGlobalMaxHeight } = sh;
  const { layers, numQueries, indexBits: nIndexBits } = sh.knobs;
  const {
    nBatches,
    maxCommitDepth,
    maxInputDepth,
    totalRow,
    nQuotientVals,
    nOpenedTrace,
  } = plan;

  const DreggProofClaim = makeDreggProofClaim(sh);
  const Digest = plan.suite.Digest;

  const privateInputs = [
    Provable.Array(BbExt, nOpenedTrace),
    Provable.Array(BbExt, nQuotientVals),
    Field, // query_pow_witness
    Provable.Array(Provable.Array(Field, totalRow), numQueries), // opened rows
    Provable.Array(Provable.Array(Provable.Array(Digest, maxInputDepth), nBatches), numQueries),
    Provable.Array(Provable.Array(BbExt, layers), numQueries), // fold siblings
    Provable.Array(Provable.Array(Provable.Array(Digest, maxCommitDepth), layers), numQueries),
    BbExt, // witnessed alpha_stark
    BbExt, // witnessed zeta
    BbExt, // witnessed fri alpha
    Provable.Array(BbExt, layers), // witnessed betas
    Provable.Array(Provable.Array(Bool, nIndexBits), numQueries), // witnessed indices
    Provable.Array(Field, NUM_CHAIN_CLAIMS), // the 25 claim lanes (exposed)
  ];

  // The step circuit (150K+ rows) needs a larger Pickles WRAP domain than the
  // maxProofsVerified=0 default (2^13). 1 → 2^14, 2 → 2^15. Env-tunable so a
  // bigger query batch can bump it without an edit.
  const overrideWrapDomain = Number(process.env.MINA_WRAP_DOMAIN ?? 1) as 0 | 1 | 2;
  // Kimchi caps ONE proof at a 2^16 domain; a 2^18 circuit (151,966 rows at one
  // query) must split into 4 chunks. Env-tunable for other query batches.
  const numChunks = Number(process.env.MINA_NUM_CHUNKS ?? 4);

  const prog = ZkProgram({
    name: `mina-shrink-verify-q${numQueries}-l${layers}-h${logGlobalMaxHeight}`,
    publicInput: DreggProofClaim,
    publicOutput: ChainClaim,
    overrideWrapDomain,
    numChunks,
    methods: {
      verifyShrink: {
        privateInputs: privateInputs as any,
        async method(
          claim: InstanceType<typeof DreggProofClaim>,
          openedTrace: BbExt[],
          openedQuotient: BbExt[],
          queryPowWitness: Field,
          rows: Field[][],
          inputPaths: Digestish[][][],
          siblings: BbExt[][],
          commitPaths: Digestish[][][],
          witAlphaStark: BbExt,
          witZeta: BbExt,
          witFriAlpha: BbExt,
          witBetas: BbExt[],
          witIndexBits: Bool[][],
          claimLanes: Field[],
        ) {
          assertProofDataInRange(claim, openedTrace, openedQuotient);
          const ch = deriveStarkChallenges(
            plan,
            claim,
            openedTrace,
            openedQuotient,
            queryPowWitness,
            {
              alphaStark: witAlphaStark,
              zeta: witZeta,
              friAlpha: witFriAlpha,
              betas: witBetas,
              queryBits: witIndexBits,
            },
          );
          // No constraints (PCS floor): assertAirClosing returns immediately.
          assertAirClosing(plan, claim, openedTrace, openedQuotient, ch);
          // THE BINDING: input-batch Merkle openings vs dregg's REAL emitted
          // Pasta commitments + the DEEP-quotient fold to the emitted final poly.
          runQueryWalk(
            plan,
            claim,
            openedTrace,
            openedQuotient,
            ch,
            rows,
            inputPaths,
            siblings,
            commitPaths,
          );
          // The claim rides beside the verify: every lane is a canonical BabyBear
          // field element (`< 2^31`), packed into the G→H ChainClaim.
          for (const l of claimLanes) assertLaneLt2p31(l);
          const chainClaim = claimOfLanes(claimLanes);
          return { publicOutput: chainClaim };
        },
      },
    },
  });

  return { prog, DreggProofClaim, ChainClaim };
}

/** Everything the driver needs to prove ONE fixture: the shape, the public
 *  claim, and the ordered private witness (12 verify items + the 25 claim
 *  lanes). */
export function shrinkProofInputs(real: any) {
  const sh = shrinkShapeOf(real);
  const v = shrinkValues(real);
  const { prog, DreggProofClaim, ChainClaim: ClaimOut } = makeMinaShrinkVerifyProgram(sh);
  const claim = rootClaim(sh, v, DreggProofClaim);
  const witness = rootWitness(sh, v);
  const claimLanes = claimLaneFields(real);
  return { sh, v, prog, DreggProofClaim, ClaimOut, claim, witness: [...witness, claimLanes] };
}

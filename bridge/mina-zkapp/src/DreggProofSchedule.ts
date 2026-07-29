import { Bool, Field, Poseidon, Provable, SelfProof, ZkProgram } from 'o1js';
import { assertLaneLt2p31 } from './Poseidon2BabyBearW16.js';
import { BbDigest } from './Poseidon2Merkle.js';
import { BbExt, assertExtInRange } from './FriQueryStep.js';
import {
  ClaimValue,
  DreggProofShape,
  StarkChallenges,
  VerifyPlan,
  assertAirClosing,
  assertProofDataInRange,
  carriedChallenges,
  deriveStarkChallenges,
  makeDreggProofClaim,
  runQueryCommitPhase,
  runQueryInputAndDeep,
  verifyPlan,
  zetaNextOf,
} from './DreggProofVerify.js';
import {
  GENESIS_CHALLENGE_DIGEST,
  challengeLanes,
  digestOfLanes,
  stepBoundary,
  terminalSeal,
} from './DreggProofPartition.js';

// ---------------------------------------------------------------------------
// THE SCHEDULED CHAIN — the cut placed where the scheduler puts it, and the
// commitment shape that lets it be put there.
//
// ⚑ WHAT §3.20 LEFT OPEN. Its chain cuts at QUERY ENTRIES, and every step
// re-derives `rootCommitDigest` from the flat lane list — so every step
// re-witnesses all 9,103 deployed root lanes, 8,920 of which are claimed opened
// evaluations that A FOLD CHAIN NEVER LOOKS AT. That is the whole of the 34,566
// rows a deployed boundary was measured to cost, and it is why the deployed step
// count came out as a 3.3x band instead of a number.
//
// ⚑ THE FIX IS THE COMMITMENT, NOT ONLY THE PLACEMENT. Commit to the VECTOR of
// chunk digests instead of to one flat list:
//
//     rootCommitDigest = Poseidon(d_0, ..., d_{m-1}),   d_i = digest of chunk i
//
// A step then witnesses the LANES of the chunks it reads and the DIGESTS of the
// chunks it does not, and re-derives the same `rootCommitDigest` either way. The
// boundary is still ONE field element, `KimchiPartition.StepPublicInput`'s three
// slots are unchanged, and a spliced chunk still moves the boundary — because it
// moves that chunk's digest, which moves the root. What changes is that a fold
// step's carry stops being a function of how big the proof is.
//
// ⚑ AND THE CUT ITSELF IS INSIDE A QUERY. §3.20's walk step is one query end to
// end. Here a query is TWO steps — its input phase and DEEP quotient, then its
// fold chain — with the boundary between them carrying the reduced openings and
// nothing else. That is the 762-row class of §3.20's table, BUILT rather than
// projected, and it is the cut `PartitionSchedule` chooses at ~99% of its
// boundaries.
//
// ⚑ ONE PROGRAM, THREE METHODS, AND THAT IS THE WALL AGAIN. §3.20 measured that
// a node process which has compiled FOUR step circuits hangs at the first
// `prove`. A transcript program plus a two-method walk program is three; adding
// a fourth method for the fold half would be four. So the transcript is a METHOD
// of the same program, every predecessor is a `SelfProof`, and what forbids a
// `fold` from following a `fold` is not the type system:
//
//   * `transcript` takes no proof and emits `Poseidon(rcd, cd, 1)`;
//   * `deep(q)` ENTERS `Poseidon(rcd, cd, 2q+1)` and EMITS
//     `Poseidon(rcd, cd_deep(q), 2q+2)`, where `cd_deep` covers the reduced
//     openings its own DEEP quotient produced;
//   * `fold(q)` ENTERS `Poseidon(rcd, cd_deep(q), 2q+2)` and EMITS
//     `Poseidon(rcd, cd, 2q+3)` — or, on the closing bit, the terminal seal.
//
// A `fold` cannot follow a `fold`, because a fold EMITS a plain challenge digest
// at an odd index and a fold ENTERS a deep digest at an even one; a `deep`
// cannot follow a `deep` for the mirror reason. The alternation, the query index
// and the chain length are all forced by the contents of ONE field element, and
// the leg exhibits each of those refusals against real proof objects.
// ---------------------------------------------------------------------------

/** How many lanes go in one chunk of the opened-evaluation group — the one free
 *  parameter of the commitment. `PartitionSchedule.bestSchedule` sweeps it at
 *  the deployed lane count; at the fixture's 56 opened lanes anything below 56
 *  gives more than one chunk, which is what keeps the leg's multi-chunk
 *  rebinding from being degenerate. */
export const DEFAULT_OPEN_CHUNK_LANES = 32;

export type LaneChunk = { id: string; lanes: Field[] };

/**
 * The proof's committed lanes, PARTITIONED.
 *
 * ⚑ THE CONCATENATION IS EXACTLY `rootCommitLanes`, IN ORDER. That is not a
 * coincidence to be maintained by hand — the leg asserts it, because a chunking
 * that dropped a lane would commit to less than the flat digest did while
 * looking identical, which is precisely the failure a "cheaper commitment"
 * invites.
 */
export function rootChunks(
  claim: ClaimValue,
  openedTrace: BbExt[],
  openedQuotient: BbExt[],
  queryPowWitness: Field,
  openChunkLanes: number = DEFAULT_OPEN_CHUNK_LANES,
): LaneChunk[] {
  const input: Field[] = [];
  for (const d of claim.inputCommits) input.push(...d.limbs);
  const fold: Field[] = [];
  for (const d of claim.commitPhaseCommits) fold.push(...d.limbs);
  for (const e of claim.finalPoly) fold.push(...e.limbs);
  const open: Field[] = [];
  for (const e of openedTrace) open.push(...e.limbs);
  for (const e of openedQuotient) open.push(...e.limbs);

  const chunks: LaneChunk[] = [
    { id: 'input', lanes: input },
    { id: 'fold', lanes: fold },
    { id: 'pub', lanes: [...claim.publicValues] },
  ];
  for (let i = 0; i * openChunkLanes < open.length; i++)
    chunks.push({ id: `open${i}`, lanes: open.slice(i * openChunkLanes, (i + 1) * openChunkLanes) });
  chunks.push({ id: 'pow', lanes: [queryPowWitness] });
  return chunks;
}

/** The chunk ids in commitment order — a step has to know which digests it must
 *  witness before it holds any values. */
export function chunkIds(plan: VerifyPlan, openChunkLanes = DEFAULT_OPEN_CHUNK_LANES): string[] {
  const openLanes = (plan.nOpenedTrace + plan.nQuotientVals) * 4;
  return [
    'input',
    'fold',
    'pub',
    ...Array.from({ length: Math.ceil(openLanes / openChunkLanes) }, (_, i) => `open${i}`),
    'pow',
  ];
}

/** `rootCommitDigest`, from the chunk digests in commitment order. */
export const rcdOfDigests = (digests: Field[]): Field => Poseidon.hash(digests);

/** `rootCommitDigest` from the whole proof — what a verifier computes out of
 *  circuit and what the transcript step computes in it. */
export const rcdOfChunks = (chunks: LaneChunk[], pack: boolean): Field =>
  rcdOfDigests(chunks.map((c) => digestOfLanes(c.lanes, pack)));

/** The lanes a `deep` step hands to its own `fold` step: the reduced openings,
 *  and nothing else. Everything else the fold chain needs is in the carried
 *  challenge set or in the `fold` chunk — which is the entire point of cutting
 *  here rather than at the query entry. */
export function deepOutLanes(ro: { ro: BbExt }[]): Field[] {
  const out: Field[] = [];
  for (const r of ro) out.push(...r.ro.limbs);
  return out;
}

/** The chain's step count: one transcript step, then two per query. */
export const scheduledSteps = (numQueries: number) => 2 * numQueries + 1;

export type ScheduleOpts = {
  pack?: boolean;
  openChunkLanes?: number;
  /** ⚑ THE CONTROL. False removes the boundary assertions and NOTHING else, so a
   *  refusal by the bound circuit is attributable to the binding rather than to
   *  the walk. It is never proved as if it verified anything. */
  bindCarry?: boolean;
};

export function makeScheduledVerify(sh: DreggProofShape, opts: ScheduleOpts = {}) {
  const pack = opts.pack ?? true;
  const bind = opts.bindCarry ?? true;
  const openChunkLanes = opts.openChunkLanes ?? DEFAULT_OPEN_CHUNK_LANES;

  const shHead: DreggProofShape = { ...sh, deriveChallenges: true };
  const shWalk: DreggProofShape = { ...sh, deriveChallenges: false, constraints: undefined };
  const planHead = verifyPlan(shHead);
  const planWalk = verifyPlan(shWalk);
  const Claim = makeDreggProofClaim(sh);
  const { layers, numQueries, indexBits: nIndexBits, finalPolyLen } = sh.knobs;
  const { nOpenedTrace, nQuotientVals, totalRow, maxInputDepth, maxCommitDepth, nBatches, nRollIns } =
    planHead;
  const ids = chunkIds(planHead, openChunkLanes);
  const nOpenChunks = ids.filter((i) => i.startsWith('open')).length;
  const nSteps = scheduledSteps(numQueries);
  const tag = `w${sh.air.width}-q${numQueries}-l${layers}-h${sh.logGlobalMaxHeight}-c${openChunkLanes}`;

  /** ⚑ THE ROLL-IN SCHEDULE IS COMPILE-TIME (`rollInSchedule`: a function of the
   *  opened matrix heights). The fold half is handed it rather than re-deriving
   *  it from heights it no longer holds, and the DEEP half's in-circuit
   *  recomputation is checked against this same list at build time. */
  const heights = [...new Set(sh.batches.flatMap((b) => b.matrices.map((m) => m.logHeight)))].sort(
    (x, y) => y - x,
  );
  const rollInRounds = heights.slice(1).map((h) => sh.logGlobalMaxHeight - 1 - h);

  /** How many chunk digests each half witnesses rather than computes. */
  const nDeepOther = ids.length - (1 + nOpenChunks); //   all but `input` + `open*`
  const nFoldOther = ids.length - 1; //                   all but `fold`

  /** The carried Fiat-Shamir set, as method arguments. Every step past the
   *  transcript re-witnesses ALL of it: a step that witnessed only what it reads
   *  could not re-derive `challengeDigest`, and the rest would then be unbound —
   *  exactly the hole §3.20's `alpha_stark` falsifier exists to catch. */
  const challengeArgs = [
    BbExt, //                                                    alpha_stark
    BbExt, //                                                    zeta
    BbExt, //                                                    fri alpha
    Provable.Array(BbExt, layers), //                            betas
    Provable.Array(Provable.Array(Bool, nIndexBits), numQueries), // query indices
  ];
  const chOf = (a: any[]): StarkChallenges =>
    carriedChallenges({ alphaStark: a[0], zeta: a[1], friAlpha: a[2], betas: a[3], queryBits: a[4] });

  /** The one-hot selector over queries, which is also the range check: without
   *  it a witnessed `q` outside `0..numQueries-1` makes every `Provable.if` fall
   *  through to query 0 and the step walks a query it was not assigned. */
  const oneHot = (q: Field): Bool[] => {
    const h = Array.from({ length: numQueries }, (_, i) => q.equals(Field(i)));
    let cnt = Field(0);
    for (const b of h) cnt = cnt.add(b.toField());
    cnt.assertEquals(Field(1));
    return h;
  };
  const selectBits = (all: Bool[][], h: Bool[]): Bool[] => {
    const out: Bool[] = [];
    for (let b = 0; b < nIndexBits; b++) {
      let cur = all[0][b];
      for (let i = 1; i < numQueries; i++) cur = Provable.if(h[i], all[i][b], cur);
      out.push(cur);
    }
    return out;
  };

  /** A step's view of the chunk digest vector: the chunks it READ, hashed from
   *  their lanes, spliced in commitment order into the chunks it did not, which
   *  arrive as digests it forwards without knowing their preimage. */
  const assembleRcd = (computed: Map<string, Field>, witnessed: Field[]): Field => {
    let w = 0;
    const v = ids.map((id) => computed.get(id) ?? witnessed[w++]);
    if (w !== witnessed.length)
      throw new Error(`the step was handed ${witnessed.length} foreign digests and used ${w}`);
    return rcdOfDigests(v);
  };

  const prog = ZkProgram({
    name: `dregg-scheduled-${tag}${bind ? '' : '-UNBOUND'}`,
    publicInput: Field,
    publicOutput: Field,
    methods: {
      /** Step 0 — absorbs the whole proof, derives the transcript, checks the AIR
       *  closing equality, and commits to every chunk. */
      transcript: {
        privateInputs: [
          Claim,
          Provable.Array(BbExt, nOpenedTrace),
          Provable.Array(BbExt, nQuotientVals),
          Field,
        ] as any,
        async method(
          bIn: Field,
          claim: ClaimValue,
          openedTrace: BbExt[],
          openedQuotient: BbExt[],
          queryPowWitness: Field,
        ) {
          assertProofDataInRange(claim, openedTrace, openedQuotient);
          const rcd = rcdOfChunks(
            rootChunks(claim, openedTrace, openedQuotient, queryPowWitness, openChunkLanes),
            pack,
          );
          stepBoundary(rcd, GENESIS_CHALLENGE_DIGEST, 0).assertEquals(bIn);

          const ch = deriveStarkChallenges(
            planHead,
            claim,
            openedTrace,
            openedQuotient,
            queryPowWitness,
          );
          assertAirClosing(planHead, claim, openedTrace, openedQuotient, ch);
          return {
            publicOutput: stepBoundary(rcd, digestOfLanes(challengeLanes(planHead, ch), pack), 1),
          };
        },
      },

      /** Step `2q+1` — query `q`'s input-phase MMCS openings and DEEP quotient:
       *  the half that READS the opened evaluations. */
      deep: {
        privateInputs: [
          SelfProof,
          Field, //                                              q
          Provable.Array(BbDigest, nBatches), //                 the `input` chunk
          Provable.Array(BbExt, nOpenedTrace), //                the `open*` chunks
          Provable.Array(BbExt, nQuotientVals),
          Provable.Array(Field, nDeepOther), //                  every other chunk's DIGEST
          ...challengeArgs,
          Provable.Array(Field, totalRow), //                    this query's opened rows
          Provable.Array(Provable.Array(BbDigest, maxInputDepth), nBatches),
        ] as any,
        async method(
          bIn: Field,
          prev: SelfProof<Field, Field>,
          q: Field,
          inputCommits: BbDigest[],
          openedTrace: BbExt[],
          openedQuotient: BbExt[],
          otherDigests: Field[],
          ...a: any[]
        ) {
          const ch = chOf(a);
          const rows: Field[] = a[5];
          const inputPaths: BbDigest[][] = a[6];
          for (const e of openedTrace) assertExtInRange(e);
          for (const e of openedQuotient) assertExtInRange(e);
          for (const d of inputCommits) for (const l of d.limbs) assertLaneLt2p31(l);

          const openAll: Field[] = [];
          for (const e of openedTrace) openAll.push(...e.limbs);
          for (const e of openedQuotient) openAll.push(...e.limbs);
          const inputLanes: Field[] = [];
          for (const d of inputCommits) inputLanes.push(...d.limbs);
          const computed = new Map<string, Field>([['input', digestOfLanes(inputLanes, pack)]]);
          for (let i = 0; i < nOpenChunks; i++)
            computed.set(
              `open${i}`,
              digestOfLanes(openAll.slice(i * openChunkLanes, (i + 1) * openChunkLanes), pack),
            );
          const rcd = assembleRcd(computed, otherDigests);
          const chal = challengeLanes(planWalk, ch);
          const k = q.mul(2).add(1);
          prev.verify();
          if (bind) {
            // (i) the boundary this step ENTERS is the one its own re-witnessed
            //     chunks imply, AT ITS OWN INDEX;
            stepBoundary(rcd, digestOfLanes(chal, pack), k).assertEquals(bIn);
            // (ii) and it is the boundary the predecessor EMITTED.
            prev.publicOutput.assertEquals(bIn);
          }

          const h = oneHot(q);
          const bits = selectBits(ch.queryBits, h);
          const deep = runQueryInputAndDeep(
            planWalk,
            { inputCommits, commitPhaseCommits: [], finalPoly: [], publicValues: [] },
            openedTrace,
            openedQuotient,
            { ...ch, queryBits: [bits] },
            zetaNextOf(planWalk, ch.zeta),
            rows,
            inputPaths,
            0,
          );
          if (deep.rollInRounds.length !== rollInRounds.length)
            throw new Error('the in-circuit roll-in schedule disagrees with the compiled one');
          // ⚑ THE INTRA-QUERY BOUNDARY. `challengeDigest` is the Fiat-Shamir
          // state entering the next step, and mid-query that state INCLUDES the
          // reduced openings — which is why this is the cheap cut: the fold half
          // needs these four field elements and none of the opened values.
          const cdDeep = digestOfLanes([...chal, ...deepOutLanes(deep.ro)], pack);
          return { publicOutput: stepBoundary(rcd, cdDeep, k.add(1)) };
        },
      },

      /** Step `2q+2` — query `q`'s fold chain: the half that reads NONE of the
       *  opened evaluations, and that asymmetry is the whole result. */
      fold: {
        privateInputs: [
          SelfProof,
          Field, //                                              q
          Bool, //                                               isLast
          Provable.Array(BbDigest, layers), //   the `fold` chunk: commit-phase...
          Provable.Array(BbExt, finalPolyLen), //                ... and final_poly
          Provable.Array(Field, nFoldOther), //                  every other chunk's DIGEST
          ...challengeArgs,
          Provable.Array(BbExt, nRollIns + 1), //  what the DEEP half handed over
          Provable.Array(BbExt, layers), //                      siblings
          Provable.Array(Provable.Array(BbDigest, maxCommitDepth), layers),
        ] as any,
        async method(
          bIn: Field,
          prev: SelfProof<Field, Field>,
          q: Field,
          isLast: Bool,
          commitPhaseCommits: BbDigest[],
          finalPoly: BbExt[],
          otherDigests: Field[],
          ...a: any[]
        ) {
          const ch = chOf(a);
          const ro: BbExt[] = a[5];
          const siblings: BbExt[] = a[6];
          const commitPaths: BbDigest[][] = a[7];
          for (const d of commitPhaseCommits) for (const l of d.limbs) assertLaneLt2p31(l);
          for (const e of finalPoly) assertExtInRange(e);
          for (const e of ro) assertExtInRange(e);

          const foldLanes: Field[] = [];
          for (const d of commitPhaseCommits) foldLanes.push(...d.limbs);
          for (const e of finalPoly) foldLanes.push(...e.limbs);
          const rcd = assembleRcd(
            new Map<string, Field>([['fold', digestOfLanes(foldLanes, pack)]]),
            otherDigests,
          );
          const chal = challengeLanes(planWalk, ch);
          const roCarried = ro.map((v) => ({ logHeight: 0, ro: v }));
          const k = q.mul(2).add(2);
          prev.verify();
          if (bind) {
            stepBoundary(rcd, digestOfLanes([...chal, ...deepOutLanes(roCarried)], pack), k)
              .assertEquals(bIn);
            prev.publicOutput.assertEquals(bIn);
          }

          const h = oneHot(q);
          const bits = selectBits(ch.queryBits, h);
          runQueryCommitPhase(
            planWalk,
            { inputCommits: [], commitPhaseCommits, finalPoly, publicValues: [] },
            { ...ch, queryBits: [bits] },
            { ro: roCarried, rollInRounds, indexAcc: Field(0) },
            siblings,
            commitPaths,
            0,
          );

          const kOut = k.add(1);
          return {
            publicOutput: Provable.if(
              isLast,
              terminalSeal(rcd, kOut),
              stepBoundary(rcd, digestOfLanes(chal, pack), kOut),
            ),
          };
        },
      },
    },
  });

  return {
    prog,
    Claim,
    planHead,
    planWalk,
    ids,
    nOpenChunks,
    nDeepOther,
    nFoldOther,
    rollInRounds,
    pack,
    bind,
    nSteps,
    numQueries,
    openChunkLanes,
    /** ⚑ THE CONTROL, BUILT FROM THE SAME SHAPE. The chain with the boundary
     *  assertions removed and nothing else changed, so it can be shown ACCEPTING
     *  what the bound one refuses. */
    unbound: () => makeScheduledVerify(sh, { ...opts, bindCarry: false }),
  };
}

// ===========================================================================
// The out-of-circuit side — the SAME functions on constants, so the harness and
// the circuit compute the boundary in one place.
// ===========================================================================

/** Everything a harness needs to drive one scheduled chain over one proof. */
export function scheduleSideOf(
  chain: ReturnType<typeof makeScheduledVerify>,
  claim: ClaimValue,
  openedTrace: BbExt[],
  openedQuotient: BbExt[],
  queryPowWitness: Field,
  ch: StarkChallenges,
) {
  const chunks = rootChunks(
    claim,
    openedTrace,
    openedQuotient,
    queryPowWitness,
    chain.openChunkLanes,
  );
  const digests = new Map(chunks.map((c) => [c.id, digestOfLanes(c.lanes, chain.pack)]));
  const rcd = rcdOfDigests(chain.ids.map((id) => digests.get(id)!));
  const chal = challengeLanes(chain.planWalk, ch);
  const cd = digestOfLanes(chal, chain.pack);
  return {
    chunks,
    digests,
    rcd,
    cd,
    chal,
    entry: stepBoundary(rcd, GENESIS_CHALLENGE_DIGEST, 0),
    /** The digests a `deep` step must be handed: every chunk it does not read. */
    deepOthers: chain.ids
      .filter((id) => id !== 'input' && !id.startsWith('open'))
      .map((id) => digests.get(id)!),
    /** The digests a `fold` step must be handed: every chunk but `fold`. */
    foldOthers: chain.ids.filter((id) => id !== 'fold').map((id) => digests.get(id)!),
    /** The boundary after the DEEP half of query `q`, given its reduced openings. */
    deepBoundary: (q: number, ro: BbExt[]) =>
      stepBoundary(
        rcd,
        digestOfLanes([...chal, ...ro.flatMap((v) => v.limbs)], chain.pack),
        2 * q + 2,
      ),
  };
}

import {
  DynamicProof,
  FeatureFlags,
  Field,
  Provable,
  VerificationKey,
  ZkProgram,
} from 'o1js';
import { canonicalLane } from './Poseidon2BabyBearW16.js';
import { BbExt } from './FriQueryStep.js';
import { UnifiedDag } from './RootAirDag.js';
import {
  ChainPlan,
  GENESIS_LIVE_DIGEST,
  digestOfLanes,
  extLanes,
  sliceCommitment,
  sliceWork,
  stepBoundary,
  terminalSeal,
} from './RootAirChain.js';

// ---------------------------------------------------------------------------
// PROCESS-PER-SLICE — one compiled circuit per process, and why it has to be
// side-loaded.
//
// §3.24 proves the largest chain ONE process holds: three slices, because a node
// process that has compiled four step circuits hangs at the first `prove`
// (kimchi's wasm heap is 32-bit; the worker dies and the promise never settles).
// The root's AIR needs SEVEN. So the chain has to cross process boundaries, and
// the only real question is what a boundary can carry.
//
// ⚑ THE OBVIOUS ARCHITECTURE DOES NOT WORK, AND THE REASON IS WORTH WRITING
// DOWN. `SelfProof` means "a proof of THIS program", so seven slices as seven
// methods of one program is seven branches compiled in every process that
// touches any of them — the wall, unchanged. Seven separate programs, each
// taking its predecessor's `Proof` class, is worse: o1js resolves a non-self
// proof type through `CompiledTag`, which exists only if the producer was
// COMPILED IN THE SAME PROCESS —
//
//     `${consumer}.compile() depends on ${producer}, but we cannot find
//      compilation output for ${producer}. Try to run ${producer}.compile() first.`
//
// — and that dependency is transitive, so compiling slice 6 means compiling
// slices 0 through 5 first. Seven compiles in one process: the wall again, by a
// longer road.
//
// ⚑ SO THE PREDECESSOR IS SIDE-LOADED. A `DynamicProof` is verified against a
// verification key that arrives as a RUNTIME INPUT, so slice k's circuit can be
// built and compiled knowing nothing about slice k−1's prover. One compile per
// process, seven processes, and the boundary is three files: the predecessor's
// proof, its verification key, and its feature flags.
//
// ⚑ AND THAT MOVES A BINDING OUT OF THE CIRCUIT, WHICH HAS TO BE PUT BACK.
// o1js says it plainly: "the circuit makes no assertions about the
// verificationKey used on its own." With a baked-in `SelfProof` the identity of
// the predecessor is a property of the compiled circuit; with a side-loaded one
// it is a value the PROVER chooses, and a prover who supplies some other
// program's proof together with that program's verification key satisfies
// `prev.verify(vk)` perfectly. The chain would still "verify" and would be
// carrying a value nothing computed.
//
// The fix is one constraint and it must be a CONSTANT, not an input:
//
//     vk.hash.assertEquals(Field(<slice k−1's verification key hash>))
//
// so slice k's circuit — and therefore slice k's OWN verification key — is a
// function of slice k−1's. The seven keys form a hash chain that ends in one
// field element a verifier pins. This is affordable for exactly the reason
// §3.24 gives for a VK per slice at all: the AIR is a FIXED program, so its
// slice keys are protocol constants emitted once, not a per-proof cost.
//
// ⚑ ONE CONSEQUENCE, STATED SO IT IS NOT DISCOVERED AS A SURPRISE. §3.21 and
// §3.24 both paid for "the unbound control has to build its own predecessor",
// because a proof made by the bound program does not verify under the unbound
// program's key. That is a fact about BAKED-IN keys. Side-loading dissolves it:
// an unbound control accepts the bound chain's own proof objects, because the
// key it verifies against is an input. The control therefore gets STRONGER here
// — it is refuting the binding on the very proofs the bound chain produced,
// rather than on a parallel chain of its own — and the thing that has to be
// separately shown is that the VK PIN is what refuses a foreign proof, which is
// what `pinVk: false` exists for.
// ---------------------------------------------------------------------------

const LANE_MAX = (1n << 31n) - 1n;

/**
 * ⚑ ONE SIDE-LOADED CLASS PER PROCESS, ENFORCED.
 *
 * `DynamicProof.tag()` names itself `o1js-sideloaded-${counter}` off a
 * process-global counter, so the identifier a second class gets depends on the
 * ORDER classes were created in — and an identifier that depends on order is an
 * identifier that differs between two processes that were supposed to compile
 * the same circuit. Every process in this architecture builds exactly one slice
 * program, so the counter is always 0; a second class is a bug that would show
 * up as a verification key that does not reproduce, which is the one thing the
 * pin cannot tolerate.
 */
let sideloadedClasses = 0;

export function makePrevProofClass(flags: FeatureFlags, maxProofsVerified: 0 | 1) {
  if (sideloadedClasses > 0)
    throw new Error(
      'a SECOND side-loaded proof class in one process: `DynamicProof.tag()` is named off a ' +
        'process-global counter, so this class would not reproduce the identifier the other ' +
        'process gave it. Build one slice program per process.',
    );
  sideloadedClasses++;
  class PrevSliceProof extends DynamicProof<Field, Field> {
    static publicInputType = Field;
    static publicOutputType = Field;
    static maxProofsVerified = maxProofsVerified;
    static featureFlags = flags;
  }
  return PrevSliceProof;
}

export type SliceOpts = {
  /** ⚑ FALSE builds the UNBOUND CONTROL — the same circuit with the boundary
   *  assertions removed. A refusal is attributable to the binding only if
   *  something shows the circuit would otherwise have ACCEPTED. */
  bindCarry?: boolean;
  /** ⚑ FALSE builds the UNPINNED CONTROL — the same circuit that still verifies
   *  its predecessor, against whatever key it is handed. This is the control for
   *  the one obligation side-loading ADDS. */
  pinVk?: boolean;
  /** Slice `si-1`'s verification key hash. Required when `si > 0` and `pinVk`. */
  prevVkHash?: bigint;
  /** Slice `si-1`'s feature flags, as its own process measured them. */
  prevFlags?: FeatureFlags;
};

/** The `maxProofsVerified` of slice `si`'s program: 0 for the opening slice,
 *  which takes no proof, and 1 for every other. */
export const sliceMaxProofsVerified = (si: number): 0 | 1 => (si === 0 ? 0 : 1);

export function sliceProgramName(si: number, n: number, opts: SliceOpts = {}) {
  const bind = opts.bindCarry !== false;
  const pin = opts.pinVk !== false;
  return `dregg-root-air-slice${si}-of${n}${bind ? '' : '-UNBOUND'}${pin ? '' : '-UNPINNED'}`;
}

/**
 * ONE slice as its own `ZkProgram` with ONE method. Slice 0 takes no proof;
 * every later slice takes its predecessor as a side-loaded `DynamicProof`
 * together with the key to verify it against, and pins that key's hash to a
 * compile-time constant.
 *
 * The boundary algebra is `RootAirChain`'s, unchanged and unforked:
 * `stepBoundary(dagDigest, liveDigest, k)` in, the same out, and
 * `terminalSeal(dagDigest, digest(acc), nSteps)` at the end. A chain built here
 * and a chain built there carry the SAME public values — which is what makes
 * §3.24's three-slice run and this one two runs of one protocol rather than two
 * protocols.
 */
export function makeSliceProgram(u: UnifiedDag, plan: ChainPlan, si: number, opts: SliceOpts = {}) {
  const bind = opts.bindCarry !== false;
  const pin = opts.pinVk !== false;
  const s = plan.slices[si];
  if (!s) throw new Error(`slice ${si} is not in a ${plan.slices.length}-slice plan`);
  const nLiveIn = s.liveIn.length;
  const nReadLanes = s.readsChunks.length * plan.chunkSize * 4;
  const nOtherDigests = plan.nColChunks - s.readsChunks.length;
  const isLast = si + 1 === plan.slices.length;
  if (si > 0 && pin && opts.prevVkHash === undefined)
    throw new Error(
      `slice ${si} pins its predecessor's verification key and was given none — an unpinned ` +
        'side-loaded chain accepts any program\'s proof and is not a chain',
    );
  if (si > 0 && !opts.prevFlags)
    throw new Error(`slice ${si} needs slice ${si - 1}'s feature flags to declare the side-loaded shape`);

  const core = (
    bIn: Field,
    prevOut: Field | null,
    alpha: BbExt,
    accIn: BbExt,
    liveInVals: BbExt[],
    readLanes: Field[],
    otherDigests: Field[],
  ): Field => {
    const dagDigest = sliceCommitment(plan, s, readLanes, otherDigests);
    for (const e of [...liveInVals, accIn, alpha])
      for (const x of e.limbs) canonicalLane(x, LANE_MAX);
    const liveInDigest =
      si === 0
        ? GENESIS_LIVE_DIGEST
        : digestOfLanes([...liveInVals.flatMap(extLanes), ...extLanes(accIn), ...extLanes(alpha)]);
    if (bind) {
      stepBoundary(dagDigest, liveInDigest, si).assertEquals(bIn);
      if (prevOut) prevOut.assertEquals(bIn);
    }
    const { acc, liveOutVals } = sliceWork(u, plan, s, alpha, accIn, liveInVals, readLanes);
    if (isLast)
      return terminalSeal(
        dagDigest,
        digestOfLanes([...extLanes(acc), ...liveOutVals.flatMap(extLanes)]),
        plan.slices.length,
      );
    return stepBoundary(
      dagDigest,
      digestOfLanes([...liveOutVals.flatMap(extLanes), ...extLanes(acc), ...extLanes(alpha)]),
      si + 1,
    );
  };

  const wide = [
    BbExt,
    BbExt,
    Provable.Array(BbExt, Math.max(nLiveIn, 1)),
    Provable.Array(Field, Math.max(nReadLanes, 1)),
    Provable.Array(Field, Math.max(nOtherDigests, 1)),
  ];

  let PrevProof: ReturnType<typeof makePrevProofClass> | null = null;
  const methods: Record<string, any> = {};
  if (si === 0) {
    methods.slice = {
      privateInputs: wide,
      async method(
        bIn: Field,
        alpha: BbExt,
        accIn: BbExt,
        liveInVals: BbExt[],
        readLanes: Field[],
        otherDigests: Field[],
      ) {
        return {
          publicOutput: core(
            bIn,
            null,
            alpha,
            accIn,
            liveInVals.slice(0, nLiveIn),
            readLanes.slice(0, nReadLanes),
            otherDigests.slice(0, nOtherDigests),
          ),
        };
      },
    };
  } else {
    const Prev = makePrevProofClass(opts.prevFlags!, sliceMaxProofsVerified(si - 1));
    PrevProof = Prev;
    const pinned = opts.prevVkHash ?? 0n;
    methods.slice = {
      privateInputs: [Prev, VerificationKey, ...wide],
      async method(
        bIn: Field,
        prev: InstanceType<typeof Prev>,
        vk: VerificationKey,
        alpha: BbExt,
        accIn: BbExt,
        liveInVals: BbExt[],
        readLanes: Field[],
        otherDigests: Field[],
      ) {
        // ⚑ THE PIN, AND IT IS THE WHOLE OF WHAT SIDE-LOADING GIVES BACK. Without
        // it `prev.verify(vk)` is satisfied by ANY program's proof paired with
        // that program's own key.
        if (pin) vk.hash.assertEquals(Field(pinned));
        prev.verify(vk);
        return {
          publicOutput: core(
            bIn,
            prev.publicOutput,
            alpha,
            accIn,
            liveInVals.slice(0, nLiveIn),
            readLanes.slice(0, nReadLanes),
            otherDigests.slice(0, nOtherDigests),
          ),
        };
      },
    };
  }

  const prog = ZkProgram({
    name: sliceProgramName(si, plan.slices.length, opts),
    publicInput: Field,
    publicOutput: Field,
    methods: methods as any,
  });

  return { prog, PrevProof, si, bind, pin, isLast };
}

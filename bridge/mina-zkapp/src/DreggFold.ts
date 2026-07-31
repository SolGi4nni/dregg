import { Field, Gadgets, SelfProof, Struct, ZkProgram } from 'o1js';
import { ChainClaim, assertClaimCarried } from './RootClaim.js';

// ---------------------------------------------------------------------------
// THE MERGE TREE — one program, one verification key, any tree shape, and NO
// SIDE-LOADED PROOF ANYWHERE. The last clause is not a preference; it is what
// o1js 2.15 allows, measured.
//
// ⚑ WHAT THIS REPLACES. The deployed chain is 912 proofs in a LINE: step k's
// witness is complete before any proof exists (`RootFriUniform.carriedLanes`
// computes both boundaries of any `(spec, q)` off the out-of-circuit
// `WalkTwin`, with no reference to a proof), and the ONLY thing that makes step
// k wait for step k-1 is `prev.verify(vk)`. A merge tree removes that edge from
// the SCHEDULE without removing it from the STATEMENT: a `FoldNode` still says
// "boundary `bIn` reaches boundary `bOut`", and a merge still refuses two nodes
// that do not touch.
//
// ===========================================================================
// ⚑ THE DESIGN THAT CANNOT BE BUILT, AND THE TEN MEASUREMENTS THAT KILLED IT
// ===========================================================================
// The obvious merge node is ONE `ZkProgram` with `lift(leafProof: DynamicProof,
// vk, vkPath)` — proving the leaf's key is a leaf under a carried `vkRoot` — and
// `merge(l: SelfProof, r: SelfProof)`. One key for both, a key TREE instead of
// per-position pins, and a driver free to fold in any order.
//
// It cannot be proved on o1js 2.15. Measured 2026-07-31 on this box, against
// real slice proofs and against minimal probes:
//
//   lift alone                            program arity 1   PROVES
//   lift + relay(1 SelfProof)             program arity 1   PROVES
//   lift + merge(2 SelfProof)             program arity 2   FAILS
//   lift + merge, leaf declared arity 2   program arity 2   FAILS (prevs_verified)
//   two side-loads in ONE branch + merge  program arity 2   FAILS
//   base(1 proof of another program) + merge                FAILS
//   pair(2 proofs of a NON-side-loading program) + merge    PROVES  (child arity 0, 1 and 2 all fine)
//   pair(2 proofs of a SIDE-LOADING program) + merge        FAILS
//   the same, with the side-loaded class at `FeatureFlags.allNone`   FAILS
//   the same, with the side-loaded class at `FeatureFlags.allMaybe`  FAILS
//
// Every failure is the same `wrap_main.ml:340` `Checked.inv` / `assert_non_zero`.
// The last two rows are there because "it is the feature flags" is the obvious
// alternative explanation and it is REFUTED: a side-loaded child declaring NO
// optional gates fails identically.
//
// Two independent rules come out of it, and the second is the one that decided
// this file:
//
//   1. A branch verifying EXACTLY ONE proof inside a program whose
//      `maxProofsVerified` is 2 cannot be proved. Branches verifying 0 or 2 are
//      fine, which is why `unit` below takes none and everything else takes two.
//   2. A side-loaded (`DynamicProof`) verification POISONS ITS WHOLE DESCENDANT
//      SUBTREE for arity 2. A proof of a program that side-loads verifies fine
//      in an arity-1 parent and fails in an arity-2 parent — so no amount of
//      intermediate programs rescues it.
//
// ⇒ **A merge tree cannot consume side-loaded leaves at all.** The key tree,
// `vkRoot`, `vkPath` and the leaf-index witness are not deferred here, they are
// DELETED, and the leaf keys are pinned the stronger way instead: `pair`
// verifies leaf proofs BY CLASS, so every admissible leaf key is baked into the
// fold's own verification key at compile time. An anchor that pins the fold key
// has pinned the whole leaf list, with no runtime comparison to get wrong.
//
// That is the ORIGINAL `constKeyPin` discipline, and the tree is what makes it
// possible: the ring the depth-8 key tree existed for — block position 0's
// predecessor is head-87 at `q = 0` and block-42 otherwise, and a ring of
// compile-time pins has no fixed point — is CUT by the tree, because a strand's
// first slice has no predecessor at all. So `Provable.Array(Field,
// VK_TREE_DEPTH)`, `leafSplit` and the `assertLeavesFit` aliasing hazard leave
// the slice body and do not reappear anywhere.
//
// ⚠⚠ WHAT THE LEAF SIDE OWES, AND IT IS NOT SMALL. TWO changes to
// `makeUniformSliceProgram`, and the SECOND is a consequence of rule 2 above
// that no one had priced:
//
//   (i)  THE INTERVAL. `pair` reads `(leaf.publicInput,
//        leaf.publicOutput.boundary)` as an interval. A slice today publishes
//        `(b_k, b_{k+1})` — ONE STEP — so a tree over 20 strand terminals would
//        span 20 steps, not 912. The strand shape is `publicInput = the
//        STRAND's entry boundary, propagated unchanged`, with the step boundary
//        checked against `prev.publicOutput` instead of against the public
//        input. Contained: two assertions move.
//
//   (ii) ⚑ THE PREDECESSOR CANNOT STAY SIDE-LOADED. Every uniform slice
//        verifies its predecessor as a `DynamicProof` (`makePrevProofClass`),
//        so by rule 2 EVERY slice proof in the deployed chain is poisoned for
//        arity 2 and can NEVER be a leaf of a merge tree. A strand's slices
//        must verify their predecessor BY CLASS — `ZkProgram.Proof(slice_{i-1})`
//        — which the tree makes possible for the first time, because cutting
//        the ring makes every remaining edge acyclic and a class pin is
//        strictly stronger than the `constKeyPin` constant it replaces.
//
//        ⚠ THE COST OF (ii) IS OPERATIONAL AND IS NOT YET MEASURED. A class pin
//        means slice i's PROGRAM OBJECT must exist in the process that compiles
//        slice i+1, so a whole strand compiles in ONE process: 88 programs for
//        the head strand, 43 for a block strand, at ~47,000 rows each. The
//        chain today compiles one program per process on purpose. Whether 88
//        Pickles prover indices fit in one process is the next measurement, and
//        it is the thing that decides whether the COARSE tree or a much
//        SHORTER strand is the right cut.
//
// ⚑ ASSOCIATIVE, AND THAT IS THE PROPERTY THE DRIVER SPENDS. dregg's own IVC
// accumulator is NOT — `circuit-prove/src/ivc_turn_chain.rs` pins
// `ordered_digest_combine_is_not_associative` as a test, because its combine is
// `acc = commit(l.acc || r.acc)` and a commitment of a commitment remembers the
// bracketing. A `FoldNode` composes as `{bIn from the left, bOut from the
// right, count added, claim equal}`, every component of which is associative.
// So a driver may fold left, fold right, work-steal, or hand a ragged tail to
// whichever worker is free, and the ROOT NODE IS THE SAME OBJECT — there is no
// shape to pin and no shape-dependent anchor.
//
// ⚑ ONE KEY FOR EVERY LEVEL. `merge` takes `SelfProof`s, so Pickles' step/wrap
// fixed point makes the program's key its own admissible child key: level 1 and
// level 9 are the same circuit under the same key.
//
// ⚑ WHAT `count` IS, SAID PLAINLY, BECAUSE IT IS THE ANCHOR'S WHOLE PIN.
// `count` counts LEAVES, not steps. `pair` emits 2, `unit` emits 0, `merge`
// adds. It is NOT a chain length and must never be described as one. What pins
// the LENGTH is the boundary chain itself: a slice's step index `k` is a
// compile-time constant (head) or tied to a one-hot query by an affine equation
// (block), and the boundary is a hash of it — so a root at `bIn == the chain's
// entry boundary` fixes the base of that induction and every later `k` follows
// by collision resistance.
//
// What `count` DOES close is the hole the terminal-seal exhibition was built
// for: the last block position emits `Provable.if(isQ[Q-1], seal, step)` under
// ONE key, so a chain that walked SIX of nineteen queries carries the identical
// claim under the identical key. Six queries is a different NUMBER OF LEAVES,
// and the anchor names the number. See `DreggFoldAnchor`.
// ---------------------------------------------------------------------------

/** `count` is range-checked to this width at every fold. 2^16 is 71x the
 *  binary tree's 912 leaves and 3,000x the coarse tree's 20, and a tree that
 *  outgrows it must say so rather than wrap. ⚠ The bound is ASSERTED; it is not
 *  inherited from the field size. dregg's own turn count had a measured forgery
 *  from exactly that inheritance — a `u64` aliasing mod BabyBear let a 2-turn
 *  history attest 6,308,233,219 — and a Pasta field is not a reason to skip a
 *  check, only a reason the same trick needs a bigger tree. */
export const FOLD_COUNT_BITS = 16;
export const FOLD_COUNT_MAX = (1 << FOLD_COUNT_BITS) - 1;

/**
 * A node of the merge tree: an interval of the boundary chain, the number of
 * leaves that cover it, and the claim they all state.
 *
 * ⚑ THERE IS NO `vkRoot` FIELD, and its absence is the design. A carried key
 * root is what a side-loaded tree needs; a class-pinned tree has the key list
 * inside its own verification key, so there is nothing for a prover to name and
 * nothing for an anchor to compare.
 */
export class FoldNode extends Struct({
  /** The boundary this interval is entered at. */
  bIn: Field,
  /** The boundary it is left at. */
  bOut: Field,
  /** How many LEAVES cover it. Not a step count — see the header. */
  count: Field,
  /** The claim every leaf under this node states. */
  claim: ChainClaim,
}) {}

/** Which obligations are armed. ⚑ Every `false` here builds a CONTROL — a
 *  program identical in width and in Pickles arity, with exactly ONE obligation
 *  removed, so a refusal is attributable to that obligation and not to the
 *  forged input being malformed elsewhere. */
export type FoldArm = {
  /** ⚑ FALSE builds the UNMERGED CONTROL: `l.bOut == r.bIn` removed, and
   *  nothing else. Its whole job is to ACCEPT a NON-ADJACENT pair. */
  adjacent?: boolean;
  /** ⚑ FALSE builds the CLAIM-DRIFT CONTROL: two halves stating different
   *  claims compose and the root states the left one. */
  carryClaim?: boolean;
  /** ⚑ FALSE builds the COUNT-FORGERY CONTROL: `count` becomes a WITNESS of
   *  the fold instead of `l.count + r.count`, so a prover names it. */
  countAdditive?: boolean;
  /** ⚑ FALSE removes the range check that keeps `count` from wrapping. */
  boundCount?: boolean;
};

export const foldArmed = (a: FoldArm) => ({
  adjacent: a.adjacent !== false,
  carryClaim: a.carryClaim !== false,
  countAdditive: a.countAdditive !== false,
  boundCount: a.boundCount !== false,
});

/**
 * **THE FIVE EQUALITIES.** Everything else a fold does is bookkeeping, and every
 * `pair` and `merge` branch discharges exactly this.
 *
 * ⚑ THIS FUNCTION IS THE ONE THE COST PROBE TIMES. `scripts/fold-mu.ts` builds
 * a two-`SelfProof` program around THIS body, not around a sketch of it, so the
 * measured mu is the fold that ships.
 */
export function assertMergeable(l: FoldNode, r: FoldNode, a: FoldArm = {}): void {
  const A = foldArmed(a);
  //  1. the intervals touch — the only thing that makes a tree a CHAIN
  if (A.adjacent) l.bOut.assertEquals(r.bIn);
  //  2-5. both halves state the same claim
  if (A.carryClaim) assertClaimCarried(l.claim, r.claim);
}

/** The composed node. ⚑ Associative in every component: `bIn` from the left,
 *  `bOut` from the right, `count` added, `claim` shared. */
export function foldCompose(
  l: FoldNode,
  r: FoldNode,
  witnessedCount: Field,
  a: FoldArm = {},
): FoldNode {
  const A = foldArmed(a);
  const count = A.countAdditive ? l.count.add(r.count) : witnessedCount;
  if (A.boundCount) Gadgets.rangeCheck16(count);
  return new FoldNode({ bIn: l.bIn, bOut: r.bOut, count, claim: l.claim });
}

/** A leaf proof, as the fold reads it: `publicInput` is the interval's start and
 *  `publicOutput` is `ClaimedBoundary`. Any `ZkProgram.Proof(sliceProgram)`
 *  with that shape is admissible. */
type LeafLike = {
  verify(): void;
  publicInput: Field;
  publicOutput: { boundary: Field; claim: ChainClaim };
};

const leafNode = (p: LeafLike): FoldNode =>
  new FoldNode({
    bIn: p.publicInput,
    bOut: p.publicOutput.boundary,
    count: Field(1),
    claim: p.publicOutput.claim,
  });

export type DreggFoldOpts = FoldArm & {
  /**
   * The distinct leaf programs, as `ZkProgram.Proof(prog)` classes, in a FIXED
   * order. ⚑ ONE `pair` METHOD PER ORDERED PAIR that actually occurs in the
   * chain — for the coarse tree that is `(head, block)` and `(block, block)`,
   * because the strands run head then nineteen query blocks. Naming them
   * explicitly is what keeps the method count at 2 instead of K².
   */
  leafClasses: { name: string; cls: any }[];
  /** Which ordered `(left, right)` leaf-class pairs get a `pair` method, by
   *  index into `leafClasses`. */
  adjacencies: [number, number][];
  suffix?: string;
};

export function dreggFoldName(o: DreggFoldOpts): string {
  const A = foldArmed(o);
  return (
    'dregg-fold' +
    (A.adjacent ? '' : '-UNMERGED') +
    (A.carryClaim ? '' : '-CLAIMDRIFT') +
    (A.countAdditive ? '' : '-COUNTFORGE') +
    (A.boundCount ? '' : '-UNBOUNDED') +
    (o.suffix ?? '')
  );
}

/**
 * **`DreggFold` — arity 2, and every branch verifies TWO proofs or NONE.**
 * That is not a style choice: see the measured table in the header.
 */
export function makeDreggFold(o: DreggFoldOpts) {
  if (o.leafClasses.length === 0)
    throw new Error(
      'makeDreggFold with no leaf classes: a fold that cannot admit a leaf is a fold over nothing. ' +
        'The leaf keys ARE the pin here — there is no runtime key list to fall back on.',
    );
  if (o.adjacencies.length === 0)
    throw new Error(
      'makeDreggFold with no adjacencies: without a `pair` method no leaf can enter the tree, and ' +
        'a 1-proof entry branch is not buildable at arity 2 (measured — see the header).',
    );

  const methods: Record<string, any> = {};

  for (const [li, ri] of o.adjacencies) {
    const L = o.leafClasses[li];
    const R = o.leafClasses[ri];
    if (L === undefined || R === undefined)
      throw new Error(`adjacency (${li}, ${ri}) names a leaf class that is not in the list`);
    methods[`pair_${L.name}_${R.name}`] = {
      privateInputs: [L.cls, R.cls, Field],
      async method(left: LeafLike, right: LeafLike, witnessedCount: Field) {
        left.verify();
        right.verify();
        const l = leafNode(left);
        const r = leafNode(right);
        assertMergeable(l, r, o);
        return { publicOutput: foldCompose(l, r, witnessedCount, o) };
      },
    };
  }

  /** Two nodes become one. ⚑ `SelfProof` on both sides is what makes the key
   *  level-independent, and it is also what makes the arity nearly free: a
   *  second verified proof in a Pickles step is ~1.04-1.13x of the first. */
  methods.merge = {
    privateInputs: [SelfProof, SelfProof, Field],
    async method(
      left: SelfProof<undefined, FoldNode>,
      right: SelfProof<undefined, FoldNode>,
      witnessedCount: Field,
    ) {
      left.verify();
      right.verify();
      const l = left.publicOutput;
      const r = right.publicOutput;
      assertMergeable(l, r, o);
      return { publicOutput: foldCompose(l, r, witnessedCount, o) };
    },
  };

  /**
   * **THE IDENTITY**, and it is what makes a RAGGED tree buildable without a
   * 1-proof branch. A zero-length interval: `bIn == bOut`, `count == 0`.
   *
   * ⚑ IT MINTS NOTHING. Folding it against a real node forces
   * `unit.bOut == real.bIn` (so its boundary is the real one's) and the claims
   * equal (so it copies), and adds 0 to the count — the composed node is
   * byte-for-byte the real one. A tree of nothing but units has `count == 0` and
   * `bIn == bOut`, which the anchor refuses on `count == FOLD_LEAVES` and on
   * `bIn == CHAIN_ENTRY_BOUNDARY`.
   *
   * ⚑ AND IT IS 0 PROOFS ON PURPOSE. A 1-proof "promote this single leaf"
   * branch is exactly the shape that cannot be proved at arity 2, so the
   * identity is how an odd tail reaches the root.
   */
  methods.unit = {
    privateInputs: [Field, ChainClaim],
    async method(b: Field, claim: ChainClaim) {
      return { publicOutput: new FoldNode({ bIn: b, bOut: b, count: Field(0), claim }) };
    },
  };

  const prog = ZkProgram({
    name: dreggFoldName(o),
    publicOutput: FoldNode,
    methods: methods as any,
  });

  return {
    prog,
    name: dreggFoldName(o),
    arm: foldArmed(o),
    pairName: (li: number, ri: number) =>
      `pair_${o.leafClasses[li].name}_${o.leafClasses[ri].name}`,
  };
}

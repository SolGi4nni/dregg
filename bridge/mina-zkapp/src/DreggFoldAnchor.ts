import {
  DeployArgs,
  DynamicProof,
  FeatureFlags,
  Field,
  Provable,
  SmartContract,
  State,
  Undefined,
  VerificationKey,
  method,
  state,
} from 'o1js';
import { ChainClaim } from './RootClaim.js';
import { FoldNode } from './DreggFold.js';
import {
  DreggBootstrap,
  bootstrapHistory,
  historyLink,
} from './DreggHeadAnchor.js';

// ---------------------------------------------------------------------------
// THE ANCHOR, AFTER THE TREE — three comparisons, all in the clear.
//
// ⚑ THIS SUPERSEDES `DreggHeadGate`, AND THE THING IT DELETES IS THE ONE THE
// CALLER HAD TO CARRY. `DreggHeadGate.advanceHead` takes `(friCommit,
// accOutDigest)` and recomputes `airTerminalSeal(friCommit,
// Poseidon(accOutDigest, chainVkRoot), totalSteps)` because the chain's LENGTH
// is not visible in a terminal proof: the last block position emits
// `Provable.if(isQ[Q-1], seal, step)` under ONE key, so a chain that walked SIX
// of nineteen queries carries the identical claim under the identical key and
// only the seal preimage tells the two apart. `terminalSealPreimage` and
// `assertOpensTerminalSeal` exist to emit and round-trip that preimage; a
// `DreggChainSeal` file exists to carry it; `devnet-head-advance` exhibits it.
// All of that is machinery for a length that nothing states.
//
// A fold root STATES it. `FoldNode.count` is in the public output, so:
//
//     vk.hash    == FOLD_VK_HASH          the root was made by the fold program
//     node.count == FOLD_LEAVES           the tree covered the whole chain
//     node.bIn   == CHAIN_ENTRY_BOUNDARY  it started where the chain starts
//
// and then `node.claim` is read. Nothing is exhibited, nothing is recomputed
// from a preimage, and the six-of-nineteen proof is refused by a comparison a
// human can check by eye: six query strands plus a head strand is SEVEN leaves,
// not twenty.
//
// ⚑ AND THERE IS NO `chainVkRoot` LINE, WHICH IS A STRENGTHENING, NOT A GAP.
// `DreggFold.pair` verifies leaf proofs BY CLASS, so every admissible leaf key
// is inside the fold's own verification key. `vk.hash == FOLD_VK_HASH` therefore
// pins the entire leaf list at compile time — there is no carried key root for a
// prover to name and no runtime comparison to get wrong. The old gate compared a
// `chainVkRoot` the PROVER supplied; this one does not have to.
//
// ⚑ WHAT `count` IS NOT. It counts LIFTED LEAVES, not chain steps. The chain's
// LENGTH is pinned the way it always was — by the boundary chain, since a
// slice's public input is `stepBoundary(friCommit, digest, k)` with `k` baked
// (head) or tied to a one-hot query (block), and `bIn == CHAIN_ENTRY_BOUNDARY`
// fixes the base of that induction. `count` pins the PARTITION: how many
// intervals were presented. Both are needed and neither implies the other, and
// writing `count == 912` when the coarse tree's count is 20 would be a pin that
// silently never matches.
//
// ⚑ WHAT DIES WHEN THE FOLD CHAIN IS PROVED. `DreggHeadGate`, its
// `(friCommit, accOutDigest)` parameters, `TerminalSealPreimage`,
// `terminalSealPreimage`, `assertOpensTerminalSeal`, `terminalSealOf`,
// `accOutDigestOf`, `dregg-chain-seal.json` and the `--seal` plumbing in
// `devnet-head-advance`. They are not kept "for compatibility" — they are kept
// until a fold root exists, because deleting the only working path before its
// replacement can be proved would leave the tree with no gate at all. The
// moment `scripts/fold-chain.ts` emits a real root, that list is one commit.
// ---------------------------------------------------------------------------

/**
 * The chain's ROOT proof, side-loaded. ⚑ `maxProofsVerified = 2`, because
 * `DreggFold.merge` verifies two `SelfProof`s and o1js takes the maximum over a
 * program's branches. `DreggTerminalProof` declares 1 and a fold root would be
 * REFUSED by it — that mismatch is a real one and is why this is a new class
 * rather than a re-pointed old one.
 */
export class DreggFoldRootProof extends DynamicProof<undefined, FoldNode> {
  //  ⚑ `Undefined`, NOT `undefined`. `DreggFold` has no public input, and o1js
  //  spells that as the `Undefined` provable; a literal `undefined` here makes
  //  `fromJSON` die in `proof.js` on `get provable`, which reads as a broken
  //  harness rather than a shape mismatch.
  static publicInputType = Undefined as any;
  static publicOutputType = FoldNode;
  static maxProofsVerified = 2 as const;
  static featureFlags = FeatureFlags.allMaybe;
}

/**
 * What this gate refuses to take on trust. Emitted by the run that compiles the
 * fold program and the chain; never typed by hand.
 */
export type DreggFoldPins = {
  label: string;
  /** `vk.hash` of `DreggFold` — ONE key for every branch and every level, and
   *  the leaf programs' keys are inside it. */
  foldVkHash: bigint;
  /** How many LEAVES a complete tree over this chain has. Coarse tree: one per
   *  strand. Binary tree: one per step. ⚠ It is a partition size, not a length. */
  foldLeaves: number;
  /** The boundary the chain's FIRST step is entered at. */
  chainEntryBoundary: bigint;
  /** `packLanes(first_old8)` of dregg's genesis anchor — the weak-subjectivity
   *  anchor, IN THE VERIFICATION KEY. */
  genesisRoot: bigint;
};

/**
 * ⚑ A PIN FILE IS A MEASUREMENT AND MUST LOOK LIKE ONE. Same discipline as
 * `assertRealPins`: a zero anywhere means the emitting run did not happen, and a
 * gate that fell back to a stand-in pin is a gate that cannot go red.
 */
export function assertRealFoldPins(p: DreggFoldPins): DreggFoldPins {
  const zero: string[] = [];
  if (p.foldVkHash === 0n) zero.push('foldVkHash');
  if (p.chainEntryBoundary === 0n) zero.push('chainEntryBoundary');
  if (p.genesisRoot === 0n) zero.push('genesisRoot');
  if (zero.length > 0)
    throw new Error(
      `DreggFoldPins: ${zero.join(', ')} ${zero.length === 1 ? 'is' : 'are'} zero. A pin file with a ` +
        'zero in it is a run that did not happen; this gate does not compile against one.',
    );
  if (!Number.isInteger(p.foldLeaves) || p.foldLeaves < 2)
    throw new Error(
      `DreggFoldPins: foldLeaves = ${p.foldLeaves}. A tree with fewer than two leaves has no merge ` +
        'in it, and a gate that pinned 1 would accept a single lifted slice as the whole chain.',
    );
  if (p.foldLeaves > 0xffff)
    throw new Error(
      `DreggFoldPins: foldLeaves = ${p.foldLeaves} exceeds the 16-bit bound every merge range-checks ` +
        '(`FOLD_COUNT_BITS`). Raise the bound in `DreggFold` and re-emit every key.',
    );
  return p;
}

export type FoldGateOpts = {
  /** ⚑ FALSE builds the UNPINNED CONTROL — any program's root is accepted. */
  pinVk?: boolean;
  /** ⚑ FALSE builds the UNCOUNTED CONTROL — the `count` comparison removed, and
   *  nothing else. Its whole job is to ACCEPT a partial tree the counted gate
   *  refuses, so the refusal is attributable to `count` rather than to the
   *  partial tree being malformed somewhere else. */
  requireCount?: boolean;
  /** ⚑ FALSE builds the UNROOTED CONTROL — the `bIn` comparison removed, so a
   *  tree that starts in the middle of the chain is accepted. */
  requireEntry?: boolean;
};

let built: string | null = null;

/** Test-only: `o1js` identifies a contract by its class and both would be named
 *  `DreggFoldGate`, so the factory refuses a second build at different pins. */
export function __resetFoldGateFactoryForTest() {
  built = null;
}

export function makeDreggFoldGate(rawPins: DreggFoldPins, opts: FoldGateOpts = {}) {
  const pins = assertRealFoldPins(rawPins);
  const pinVk = opts.pinVk !== false;
  const requireCount = opts.requireCount !== false;
  const requireEntry = opts.requireEntry !== false;
  const fingerprint =
    `${pins.foldVkHash}/${pins.foldLeaves}/${pins.chainEntryBoundary}` +
    `/${pins.genesisRoot}/${pinVk}/${requireCount}/${requireEntry}`;
  if (built !== null && built !== fingerprint)
    throw new Error(
      'a SECOND DreggFoldGate at DIFFERENT pins in one process: o1js identifies a contract by its ' +
        'class and both would be named `DreggFoldGate`. Build one gate per process.',
    );
  built = fingerprint;

  const FOLD_VK_HASH = Field(pins.foldVkHash);
  const FOLD_LEAVES = Field(pins.foldLeaves);
  const CHAIN_ENTRY_BOUNDARY = Field(pins.chainEntryBoundary);
  const GENESIS_ROOT = Field(pins.genesisRoot);

  const variant =
    'DreggFoldGate' +
    (pinVk ? '' : '-UNPINNED') +
    (requireCount ? '' : '-UNCOUNTED') +
    (requireEntry ? '' : '-UNROOTED');

  /**
   * **THE FOUR LINES.** Everything the old gate did with a preimage, done with
   * comparisons against fields the root proof publishes.
   */
  function openRoot(root: DreggFoldRootProof, vk: VerificationKey): ChainClaim {
    if (pinVk)
      vk.hash.assertEquals(
        FOLD_VK_HASH,
        'DreggFoldGate: the root was made under a key this gate does not name',
      );
    root.verify(vk);
    const node = root.publicOutput;
    if (requireCount)
      node.count.assertEquals(
        FOLD_LEAVES,
        'DreggFoldGate: the tree does not cover the whole chain — wrong number of leaves',
      );
    if (requireEntry)
      node.bIn.assertEquals(
        CHAIN_ENTRY_BOUNDARY,
        'DreggFoldGate: the tree does not start at the chain\'s entry boundary',
      );
    return node.claim;
  }

  class DreggFoldGate extends SmartContract {
    @state(Field) head = State<Field>();
    @state(Field) prevHead = State<Field>();
    @state(Field) turns = State<Field>();
    @state(Field) lastSegmentTurns = State<Field>();
    @state(Field) acceptedHistory = State<Field>();
    @state(Field) fork = State<Field>();

    async deploy(props?: DeployArgs & { bootstrap?: DreggBootstrap }) {
      await super.deploy(props);
      const b = props?.bootstrap;
      if (b === undefined || b.provenance !== 'weak-subjectivity-anchor')
        throw new Error(
          'DreggFoldGate.deploy({ bootstrap }) requires a DreggBootstrap from ' +
            '`DreggBootstrap.weakSubjectivityAnchor(...)`. The first head has nothing before it ' +
            'and nothing can verify it; naming that is not optional.',
        );
      if (!b.genesisRoot.equals(GENESIS_ROOT).toBoolean())
        throw new Error(
          'DreggFoldGate.deploy: the bootstrap anchor is not the genesis root this gate was ' +
            'compiled against. The pin is IN the verification key; a deploy at another anchor is ' +
            'a different contract.',
        );
      this.head.set(b.genesisRoot);
      this.prevHead.set(Field(0));
      this.turns.set(Field(0));
      this.lastSegmentTurns.set(Field(0));
      this.acceptedHistory.set(bootstrapHistory(b.genesisRoot));
      this.fork.set(Field(0));
    }

    /**
     * **THE ADVANCE.** Two arguments where the old gate took four.
     *
     * ⚑ THE TWO THAT LEFT ARE `(friCommit, accOutDigest)` — a preimage of a hash
     * that a caller had to be handed out of band, that no proof publishes, and
     * that existed ONLY to tell a terminal boundary from a mid-chain one. The
     * root publishes `count`; the count says it.
     */
    @method async advanceHead(root: DreggFoldRootProof, vk: VerificationKey) {
      const fork = this.fork.getAndRequireEquals();
      fork.assertEquals(Field(0), 'DreggFoldGate: this client is HALTED by a recorded fork');

      const claim = openRoot(root, vk);

      const head = this.head.getAndRequireEquals();
      const turns = this.turns.getAndRequireEquals();
      const history = this.acceptedHistory.getAndRequireEquals();

      const first = turns.equals(Field(0));
      const mustStartAt = Provable.if(first, GENESIS_ROOT, head);
      claim.genesisRoot.assertEquals(
        mustStartAt,
        'DreggFoldGate: the segment does not start at this client\'s head',
      );
      claim.numTurns.assertNotEquals(Field(0));
      claim.finalRoot.assertNotEquals(Field(0));

      this.prevHead.set(head);
      this.head.set(claim.finalRoot);
      this.turns.set(turns.add(claim.numTurns));
      this.lastSegmentTurns.set(claim.numTurns);
      this.acceptedHistory.set(historyLink(history, claim));
    }
  }

  return { DreggFoldGate, variant, pins, pinVk, requireCount, requireEntry };
}

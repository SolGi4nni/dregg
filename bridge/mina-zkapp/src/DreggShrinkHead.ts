import {
  DynamicProof,
  FeatureFlags,
  Field,
  Provable,
  SmartContract,
  State,
  VerificationKey,
  method,
  state,
  type DeployArgs,
} from 'o1js';
import { ChainClaim, ClaimedBoundary } from './RootClaim.js';
import { partitionTerminalSeal } from './DreggProofPartition.js';
import {
  DreggBootstrap,
  bootstrapHistory,
  canonicalBootstrapState,
  historyLink,
  forkWitnessOf,
} from './DreggHeadAnchor.js';

// ---------------------------------------------------------------------------
// THE SHRINK-PARTITION HEAD GATE — the "one real piece of glue" between
// `MinaShrinkPartition`'s terminal and a Mina-side dregg head.
//
// ⚑ THE SEAL SEAM, RESOLVED. `DreggHeadGate` (the RootFriUniform path) pins a
// FOUR-field domain-tagged seal carrying an `accOutDigest` and a `chainVkRoot`
// ring. The shrink partition has no ring — its two VKs (step0, walk) are pinned
// at compile time by o1js's own proof typing (`walk.first` side-loads a
// `Step0Proof`, `walk.step` a `SelfProof`), so the only runtime pin is the
// TERMINAL walk VK. Its seal is therefore the partition family's THREE-field
// UNTAGGED `partitionTerminalSeal(rootCommitDigest, nSteps)`. This gate is the
// verifier for THAT seal, and it says so in its own type — a `DreggHeadGate` seal
// (four fields, `Field(1)` tag) is not exhibitable here and vice-versa.
//
// ⚑ WHAT AN ACCEPTED ADVANCE KNOWS. dregg's state went `G → H` in `N` turns with
// ordered-history commitment `D`; `G` was the head this client held; and a
// native-Pasta batch-STARK over the shrink terminal — ALL 38 FRI queries
// authenticated against dregg's OWN emitted Pasta commitments, the DEEP fold
// reaching the emitted final poly — verified for exactly that claim, with the
// claim SEALED to the authenticated opened trace (`MinaShrinkPartition
// .readSealedClaim`), not supplied to the proof.
//
// ⚑ WHAT IT DOES NOT. NOT that the codeword is low-degree (the FRI/STARK floor is
// undischarged, as everywhere). NOT that the Fiat-Shamir transcript was re-derived
// in o1js (it is CARRIED — the §3.14 residual; the derivation is Rust-side). NOT
// that `H` is what dregg FINALIZED — a segment proof establishes EXECUTABILITY
// G→H, not which executable future consensus chose, which is why `reportFork`
// halts rather than picks.
// ---------------------------------------------------------------------------

/**
 * The pins the shrink head gate refuses to take on trust — emitted by the run
 * that compiles the partition, never typed by hand.
 */
export type ShrinkChainPins = {
  /** Which terminal, at which fixture. Recorded for a deployment record. */
  label: string;
  /** `vk.hash` of the `walk` program — the terminal-position program the last
   *  query step proves. */
  terminalVkHash: bigint;
  /** `nSteps = numQueries + 1` — the chain LENGTH, so a short chain is not a
   *  terminal one. */
  totalSteps: number;
  /** `packLanes(first_old8)` of dregg's genesis state anchor — the
   *  weak-subjectivity anchor, IN THE VERIFICATION KEY. */
  genesisRoot: bigint;
};

export function assertRealShrinkPins(p: ShrinkChainPins): ShrinkChainPins {
  const bad: string[] = [];
  if (!p.label || p.label.length < 8) bad.push('label (say which terminal, at which fixture)');
  if (p.terminalVkHash === 0n) bad.push('terminalVkHash');
  if (!Number.isInteger(p.totalSteps) || p.totalSteps <= 0) bad.push('totalSteps');
  if (p.genesisRoot === 0n) bad.push('genesisRoot');
  if (bad.length)
    throw new Error(
      `ShrinkChainPins is not a measurement — ${bad.join(', ')} is absent or zero. These come out ` +
        'of the run that compiles the shrink partition; there is no default and a gate built on ' +
        'one would accept a proof of nothing.',
    );
  return p;
}

/**
 * The shrink partition's terminal proof, side-loaded. ONE `DynamicProof` class
 * per process (`DynamicProof.tag()` is process-global).
 */
export class ShrinkTerminalProof extends DynamicProof<Field, ClaimedBoundary> {
  static publicInputType = Field;
  static publicOutputType = ClaimedBoundary;
  static maxProofsVerified = 1 as const;
  static featureFlags = FeatureFlags.allMaybe;
}

let built: string | null = null;

export type ShrinkHeadGateOpts = {
  /** FALSE builds the UNPINNED control — `vk.hash.assertEquals` removed and
   *  nothing else. Never deployed. */
  pinVk?: boolean;
  /** FALSE builds the UNSEALED control — the terminal-seal exhibition removed;
   *  its whole job is to ACCEPT a mid-chain step boundary the sealed gate
   *  refuses. */
  requireSeal?: boolean;
};

export function makeShrinkHeadGate(rawPins: ShrinkChainPins, opts: ShrinkHeadGateOpts = {}) {
  const pins = assertRealShrinkPins(rawPins);
  const pinVk = opts.pinVk !== false;
  const requireSeal = opts.requireSeal !== false;
  const fingerprint =
    `${pins.terminalVkHash}/${pins.totalSteps}/${pins.genesisRoot}/${pinVk}/${requireSeal}`;
  if (built !== null && built !== fingerprint)
    throw new Error(
      'a SECOND DreggShrinkHeadGate at DIFFERENT pins in one process: o1js identifies a contract ' +
        'by its class. Build one gate per process.',
    );
  built = fingerprint;

  const TERMINAL_VK_HASH = Field(pins.terminalVkHash);
  //  ⚑ THE REFUSAL NAMES THE CIRCUIT. Same reason as `DreggHeadAnchor`'s: this
  //  tree holds THREE prover-side terminal keys (this one, and the BabyBear and
  //  Pasta RootFriUniform terminals) plus dregg's Lean-derived `KimchiWrapMain`
  //  key registered on Mina devnet, and a bare number-vs-number mismatch cannot
  //  tell them apart. A JS error string, not a constraint — the VK is unmoved.
  const WANTED_KEY =
    'DreggShrinkHeadGate: the proof was made under a key this gate does not name. It wants the ' +
    `o1js ZkProgram key of MinaShrinkPartition's TERMINAL \`walk\` for "${pins.label}", ` +
    `vk.hash ${pins.terminalVkHash}. It is NOT a RootFriUniform terminal (different seal family: ` +
    'three-field untagged `partitionTerminalSeal`, not four-field tagged `airTerminalSeal`) and ' +
    'NOT dregg\'s Lean-derived wrap key on devnet. Identify yours with `npm run vk-identity`.';
  const TOTAL_STEPS = Field(pins.totalSteps);
  const GENESIS_ROOT = Field(pins.genesisRoot);

  /**
   * The obligation both methods discharge: the proof verifies under the pinned
   * walk key, and its boundary is the partition's TERMINAL seal at the pinned
   * length over the exhibited `rootCommitDigest`.
   */
  function openTerminal(
    terminal: ShrinkTerminalProof,
    vk: VerificationKey,
    rootCommitDigest: Field,
  ): ChainClaim {
    if (pinVk) vk.hash.assertEquals(TERMINAL_VK_HASH, WANTED_KEY);
    terminal.verify(vk);
    const po = terminal.publicOutput;
    if (requireSeal)
      partitionTerminalSeal(rootCommitDigest, TOTAL_STEPS).assertEquals(
        po.boundary,
        "DreggShrinkHeadGate: the boundary is not this partition's TERMINAL seal at the pinned length",
      );
    return po.claim;
  }

  class DreggShrinkHeadGate extends SmartContract {
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
          'DreggShrinkHeadGate.deploy({ bootstrap }) requires a DreggBootstrap from ' +
            '`DreggBootstrap.weakSubjectivityAnchor(...)`.',
        );
      if (!b.genesisRoot.equals(GENESIS_ROOT).toBoolean())
        throw new Error(
          "the bootstrap anchor is not the genesis this gate's VERIFICATION KEY pins.",
        );
      const c = canonicalBootstrapState({ genesisRoot: pins.genesisRoot } as any);
      this.head.set(c.head);
      this.prevHead.set(c.prevHead);
      this.turns.set(c.turns);
      this.lastSegmentTurns.set(c.lastSegmentTurns);
      this.acceptedHistory.set(c.acceptedHistory);
      this.fork.set(c.fork);
    }

    /** Move the head because dregg's shrink partition said so. */
    @method async advanceHead(
      terminal: ShrinkTerminalProof,
      vk: VerificationKey,
      rootCommitDigest: Field,
    ) {
      const fork = this.fork.getAndRequireEquals();
      fork.assertEquals(Field(0), 'DreggShrinkHeadGate: this client is HALTED by a recorded fork');

      const claim = openTerminal(terminal, vk, rootCommitDigest);

      const head = this.head.getAndRequireEquals();
      const turns = this.turns.getAndRequireEquals();
      const history = this.acceptedHistory.getAndRequireEquals();

      //  First segment starts at the pinned genesis; every later one at the head
      //  an accepted proof left.
      const first = turns.equals(Field(0));
      const mustStartAt = Provable.if(first, GENESIS_ROOT, head);
      claim.genesisRoot.assertEquals(
        mustStartAt,
        "DreggShrinkHeadGate: the segment does not start at this client's head",
      );
      claim.numTurns.assertNotEquals(Field(0));
      claim.finalRoot.assertNotEquals(Field(0));

      this.prevHead.set(head);
      this.head.set(claim.finalRoot);
      this.turns.set(turns.add(claim.numTurns));
      this.lastSegmentTurns.set(claim.numTurns);
      this.acceptedHistory.set(historyLink(history, claim));
    }

    /** A proof the state machine equivocated where this client committed. */
    @method async reportFork(
      terminal: ShrinkTerminalProof,
      vk: VerificationKey,
      rootCommitDigest: Field,
    ) {
      const fork = this.fork.getAndRequireEquals();
      fork.assertEquals(Field(0), 'DreggShrinkHeadGate: a fork witness is already recorded');

      const claim = openTerminal(terminal, vk, rootCommitDigest);

      const head = this.head.getAndRequireEquals();
      const prevHead = this.prevHead.getAndRequireEquals();
      const turns = this.turns.getAndRequireEquals();
      const lastTurns = this.lastSegmentTurns.getAndRequireEquals();

      turns.assertNotEquals(
        Field(0),
        'DreggShrinkHeadGate: nothing has been accepted yet, so nothing can conflict with it',
      );
      claim.genesisRoot.assertEquals(
        prevHead,
        'DreggShrinkHeadGate: a fork report must start where the last accepted segment started',
      );
      claim.numTurns.assertEquals(
        lastTurns,
        'DreggShrinkHeadGate: a fork report must be the SAME LENGTH — a different length is a prefix',
      );
      claim.finalRoot.assertNotEquals(
        head,
        'DreggShrinkHeadGate: this is the segment already accepted, not a conflicting one',
      );

      this.fork.set(forkWitnessOf(claim));
    }
  }

  return {
    DreggShrinkHeadGate,
    pins,
    pinVk,
    requireSeal,
    variant:
      pinVk && requireSeal
        ? 'GATE'
        : `CONTROL(${pinVk ? '' : 'UNPINNED '}${requireSeal ? '' : 'UNSEALED'})`.trim(),
    TERMINAL_VK_HASH,
    TOTAL_STEPS,
    GENESIS_ROOT,
    bootstrapHistory,
  };
}

/** TEST-ONLY — lets one process build a second gate at different pins. */
export function __resetShrinkHeadGateFactoryForTest() {
  built = null;
}

import {
  DynamicProof,
  FeatureFlags,
  Field,
  Poseidon,
  Provable,
  SmartContract,
  State,
  VerificationKey,
  method,
  state,
  type DeployArgs,
} from 'o1js';
import { ChainClaim, ClaimedBoundary } from './RootClaim.js';
import { digestOfLanes } from './RootAirChain.js';
import { taggedTerminalSeal } from './CostModel.js';

// ---------------------------------------------------------------------------
// THE PROOF-GATED ANCHOR — a Mina-side dregg light client whose head advances
// because a proof verified, and whose only key act is its own bootstrap.
//
// ⚑ WHAT THIS REPLACES, AND WHY IT IS NOT AN EDIT OF IT.
// `DreggAttestedGate.setDreggRoot(anchor, placeholderAuth)` anchors a root
// because a NAMED KEY SIGNED the transition. Its own header says so in as many
// words: the proof obligation is a SHAPE constraint ("the anchored value is the
// Mina image of a real BabyBear MMCS root — anyone can build a Merkle tree") and
// `placeholderAuth` is "the ONLY thing that currently makes the anchor
// unforgeable". That contract is UNTOUCHED by this file, deliberately: an
// ungated anchor is strictly worse than a labelled one, and the two live side by
// side until the proof path has run end to end on Devnet. `PLACEHOLDER_CUTOVER`
// below is the retirement plan, written down rather than intended.
//
// ⚑ WHAT MAKES THE OBLIGATION STAND ALONE HERE. The proof this gate consumes is
// the terminal proof of dregg's own root-proof verification chain — the object
// `RootFriUniform` builds — and since §3.30 that proof's PUBLIC OUTPUT is a
// `ClaimedBoundary`: a boundary field beside `(genesisRoot G, finalRoot H,
// numTurns N, chainDigest D)`, all four READ OFF the proof rather than supplied
// to it. So "any caller who can produce the proof" stops being a hole and starts
// being exactly the property wanted: producing it means walking dregg's root
// FRI-STARK.
//
// ⚑ THREE THINGS ARE PINNED, AND EACH CLOSES A DIFFERENT DOOR.
//
//   1. `vk.hash == terminalVkHash`. o1js says it plainly — a `DynamicProof`
//      circuit "makes no assertions about the verificationKey used on its own"
//      — so without this the gate verifies SOME program's proof and calls it
//      dregg's. This is the same pin `538177684` made load-bearing in the AIR
//      chain, at the same resolution: unpinned ACCEPTS a foreign proof, and that
//      control is live.
//   2. The TERMINAL SEAL is EXHIBITED, not assumed. The chain's last block
//      position emits `Provable.if(isQ[Q-1], seal, step)` — the SAME program,
//      and therefore the SAME verification key, at every query. A proof of that
//      program at q = 5 is a chain that walked SIX of nineteen queries and
//      carries the identical claim. Pinning the key alone would accept it. So
//      the caller exhibits the seal's preimage and the gate recomputes
//      `airTerminalSeal(friCommit, Poseidon(accOutDigest, chainVkRoot),
//      totalSteps)` and compares. `airTerminalSeal` is FOUR fields with a
//      trailing `Field(1)`; `stepBoundary` is three; they are domain-separated
//      by construction (`CostModel.taggedTerminalSeal` vs `chainStepBoundary`),
//      so a step boundary is not exhibitable as a seal under collision
//      resistance.
//   3. `chainVkRoot` rides INSIDE that preimage, so the whole key list is the
//      protocol's. `RootFriUniform`'s header: a uniform block is a RING and a
//      ring of compile-time key pins has no fixed point, so each slice proves
//      its predecessor's `vk.hash` at a fixed leaf under a carried Merkle root —
//      and "the root is anchored where the verifier already looks: the TERMINAL
//      SEAL carries it". This gate is that verifier. A prover who substitutes a
//      key list produces a seal that does not match a pin.
//
// ⚑ AND THE PINS LIVE IN THE VERIFICATION KEY, NOT IN STATE. `placeholderRelay`
// is a state field written once by a signature-authorized deploy; anything in
// that position is an operator assertion. Baking the pins into the circuit makes
// the DEPLOYED ADDRESS commit to which chain it will accept: rotating dregg's
// key list rotates this zkApp's VK and therefore its address, which is a visible
// flag day rather than a silent state write. That is why this is a FACTORY.
//
// ⚑ WHAT THE ZKAPP KNOWS AFTER AN ACCEPTED ADVANCE, in one sentence:
//
//     dregg's state went from `G` to `H` in `N` turns with ordered-history
//     commitment `D`, `G` was the head this client already held, and a
//     batch-STARK over the root's seven AIRs — closing equalities at values
//     dregg committed to, FRI walk at a transcript derived from the batch
//     itself, all nineteen queries — verified for exactly that claim.
//
// ⚑ AND WHAT IT DOES NOT, at the resolution the arc measured rather than as a
// caveat paragraph:
//
//   * NOT that the committed function is low degree. The FRI/STARK soundness
//     floor is exactly as undischarged here as everywhere else in this tree; a
//     Kimchi proof that a FRI verifier ACCEPTED is not a proof that the codeword
//     is near a low-degree one.
//   * NOT that `H` is the head dregg FINALIZED. A segment proof establishes that
//     `N` turns are EXECUTABLE from `G` to `H`; which of several executable
//     futures is canonical is dregg's consensus's answer, and no committee
//     signature, blocklace certificate or finality evidence rides in this proof.
//     `reportFork` exists because of exactly this and is the honest consequence.
//   * NOT that the 25 `expose_claim` lanes are what the AIR's own constraints
//     FORCE. The chain proves the closing equalities hold at the opened values;
//     that `public[i]` IS the fold of the real wide descriptor leaves is the Rust
//     host's tooth (`ivc_turn_chain.rs:3096-3115`), not this chain's.
//   * NOT anything about the 192 LogUp constraints, which are still outside the
//     DAG vocabulary the AIR half compiles (§3.18).
//
// ⚑ WHERE THE TRUST ACTUALLY TERMINATES. The terminal proof attests a chain of
// slices whose BOTTOM is `airTerminalSeal(dagDigest, …, AIR_SLICES)` — the AIR
// chain's own seal, entered by head slice 0 against a COMPILE-TIME key pin. So
// the induction bottoms out at (a) two compile-time constants in this file, (b)
// the AIR chain's genesis constant, and (c) Kimchi/Pickles' own soundness. It
// does NOT bottom out at anything a person signed, once the bootstrap below has
// happened.
// ---------------------------------------------------------------------------

/** Pack up to 31 ASCII bytes into one Pasta field, big-endian — the shape
 *  `devnet-root.json`'s domain-tag leaf already uses. */
function tagField(s: string): Field {
  const bytes = new TextEncoder().encode(s);
  if (bytes.length === 0 || bytes.length > 31)
    throw new Error(`a domain tag is 1..31 ASCII bytes and '${s}' is ${bytes.length}`);
  let acc = 0n;
  for (const b of bytes) acc = (acc << 8n) | BigInt(b);
  return Field(acc);
}

/** Domain tags. Three DISTINCT ones, because the three hashes below would
 *  otherwise share an image and a fork witness could be mistaken for a history
 *  link by anything that reads state without reading this file. */
export const HEAD_TAGS = {
  bootstrap: tagField('dregg/mina-head/bootstrap/v1'),
  history: tagField('dregg/mina-head/history/v1'),
  fork: tagField('dregg/mina-head/fork/v1'),
} as const;

// ===========================================================================
// 1. The proof this gate consumes.
// ===========================================================================

/**
 * The terminal proof of dregg's root-proof verification chain, side-loaded.
 *
 * ⚑ ONE `DynamicProof` CLASS PER PROCESS. `DynamicProof.tag()` names itself off
 * a process-global counter, so a second class in one process gets an identifier
 * that depends on creation ORDER — `RootFriUniform.makePrevProofClass` throws on
 * a second one for exactly this reason. A process that builds a slice program
 * must not also build this gate, and the leg keeps them in separate processes.
 *
 * ⚑ `allMaybe` IS A DECISION, and it is the same one `root-fri-uniform.ts`
 * records: it costs verifier-circuit GENERALITY and not IDENTITY, which the key
 * pin supplies. The terminal program's real flags are on disk
 * (`.fullchain/fri-flags-*.json`, `{rangeCheck0, lookup}` at the deployed hash);
 * narrowing to them is a row-count optimisation this gate has not measured and
 * therefore does not claim.
 */
export class DreggTerminalProof extends DynamicProof<Field, ClaimedBoundary> {
  static publicInputType = Field;
  static publicOutputType = ClaimedBoundary;
  static maxProofsVerified = 1 as const;
  static featureFlags = FeatureFlags.allMaybe;
}

// ===========================================================================
// 2. The pins — the protocol constants that go INTO the verification key.
// ===========================================================================

/**
 * Everything about dregg's verification chain that this gate refuses to take on
 * trust. Emitted by the run that compiles the chain; never typed by hand.
 *
 * ⚑ NO DEFAULTS AND NO PLACEHOLDER VALUES. `assertRealPins` refuses a zero, and
 * `makeDreggHeadGate` calls it before it builds anything. A gate that fell back
 * to a stand-in pin would be a gate that cannot go red — the class this repo
 * keeps paying for.
 */
export type DreggChainPins = {
  /** Which chain these came from, and at which hash. Recorded, never checked —
   *  it is for the reader of a deployment record, not for the circuit. */
  label: string;
  /** `vk.hash` of the chain's TERMINAL-POSITION program — the block's last
   *  position, `uniformProgramName({kind:'block', pos: |block|-1}, …)`. */
  terminalVkHash: bigint;
  /** The `VK_TREE_DEPTH`-deep Merkle root over the chain's whole key list, the
   *  value `RootFriUniform` carries and seals. */
  chainVkRoot: bigint;
  /** `totalSteps(plan) = AIR_SLICES + plan.totalSlices` — the chain's LENGTH, so
   *  a short chain is not a terminal one. */
  totalSteps: number;
  /** `packLanes(first_old8)` of dregg's genesis state anchor: the weak-
   *  subjectivity anchor, IN THE VERIFICATION KEY. */
  genesisRoot: bigint;
};

/**
 * ⚑ THE PIN FILE IS A MEASUREMENT AND MUST LOOK LIKE ONE. A zero anywhere means
 * the emitting run did not happen; refusing here is what keeps a compiled-but-
 * unpinned gate from existing at all.
 *
 * ⚠ ONE CONSISTENCY THIS CANNOT CHECK and the EMITTER MUST: `terminalVkHash` has
 * to be the leaf sitting at the terminal position's fixed index under
 * `chainVkRoot`. Pinning both independently is strictly stronger than pinning
 * either — a prover must satisfy both — but a pin file whose two halves come
 * from DIFFERENT chains would make the gate unusable rather than unsound, and
 * "unusable" is not a state anyone should discover on chain.
 */
export function assertRealPins(p: DreggChainPins): DreggChainPins {
  const bad: string[] = [];
  if (!p.label || p.label.length < 8) bad.push('label (say which chain, at which hash)');
  if (p.terminalVkHash === 0n) bad.push('terminalVkHash');
  if (p.chainVkRoot === 0n) bad.push('chainVkRoot');
  if (!Number.isInteger(p.totalSteps) || p.totalSteps <= 0) bad.push('totalSteps');
  if (p.genesisRoot === 0n) bad.push('genesisRoot');
  if (bad.length)
    throw new Error(
      `DreggChainPins is not a measurement — ${bad.join(', ')} is absent or zero. These come out ` +
        'of the run that compiles dregg\'s verification chain; there is no default and a gate ' +
        'built on one would accept a proof of nothing.',
    );
  return p;
}

// ===========================================================================
// 3. The bootstrap — un-gated by nature, and saying so in the type.
// ===========================================================================

/**
 * **THE WEAK-SUBJECTIVITY ANCHOR.** The first head has nothing before it, so
 * nothing can verify it. This is the same object as `cosmos-lightclient`'s
 * `TrustedCosmosState::weak_subjectivity_anchor` and the ETH light client's
 * `pin_genesis_committee`: an operator asserting out of band what no cryptography
 * can check.
 *
 * ⚑ IT IS NOT GATED AND IT DOES NOT PRETEND TO BE. What the type buys is that
 * the assertion cannot happen by accident and cannot be confused with an
 * advance: the constructor is private, the ONE way in is named for what it is,
 * and `provenance` is on the object so a deployment record carries it.
 *
 * ⚑ AND THE CIRCUIT NARROWS IT ANYWAY. `advanceHead` requires the FIRST accepted
 * segment to start at `pins.genesisRoot`, which is a compile-time constant — so
 * a deployer who writes a wrong `head` into state at `turns = 0` has written
 * something no advance will ever build on. What the deploy CAN still assert
 * unilaterally is a non-zero `turns` with a chosen `head`: that is the anchor
 * proper, it is exactly as trusted as it sounds, and `bootstrapProvenance`
 * reads it back off a deployed account so a third party can tell which happened.
 */
export class DreggBootstrap {
  readonly provenance = 'weak-subjectivity-anchor' as const;
  private constructor(
    readonly genesisRoot: Field,
    /** Why this operator believes this genesis. Free text, recorded on the
     *  deployment record, checked by nothing — which is the point. */
    readonly attestation: string,
  ) {}

  /**
   * The ONE constructor. Named for the trust it takes rather than for what it
   * does, because the name is the only warning a reader gets.
   */
  static weakSubjectivityAnchor(genesisRoot: Field, attestation: string): DreggBootstrap {
    if (attestation.trim().length < 16)
      throw new Error(
        'DreggBootstrap.weakSubjectivityAnchor requires an attestation of at least 16 characters: ' +
          'this is the one thing in the gate that no proof checks, so it says who asserted it.',
      );
    if (genesisRoot.equals(Field(0)).toBoolean())
      throw new Error('the genesis anchor is zero — that is an absent anchor, not a chosen one');
    return new DreggBootstrap(genesisRoot, attestation);
  }
}

/** The first link of the client's receipt chain: an empty history at a named
 *  genesis. ONE definition, called by the contract's `deploy` and by any audit
 *  that reads a deployed account back. */
export const bootstrapHistory = (genesisRoot: Field): Field =>
  Poseidon.hash([HEAD_TAGS.bootstrap, genesisRoot]);

/** The six state values an HONEST bootstrap writes, given the pins. A deployer
 *  who writes anything else has asserted a head, and `bootstrapProvenance` says
 *  so out loud. */
export function canonicalBootstrapState(pins: DreggChainPins) {
  const g = Field(pins.genesisRoot);
  return {
    head: g,
    prevHead: g,
    turns: Field(0),
    lastSegmentTurns: Field(0),
    acceptedHistory: bootstrapHistory(g),
    fork: Field(0),
  };
}

/**
 * Read a DEPLOYED account's state back and say which of three things it is.
 *
 * ⚑ THREE-VALUED ON PURPOSE. "Not the canonical genesis" is not the same finding
 * as "halted", and neither is the same as "fine"; collapsing them is how a fork
 * halt gets read as a bad deploy.
 */
export function bootstrapProvenance(
  observed: { head: Field; prevHead: Field; turns: Field; acceptedHistory: Field; fork: Field },
  pins: DreggChainPins,
): { verdict: 'genesis' | 'operator-asserted-head' | 'halted'; why: string } {
  if (!observed.fork.equals(Field(0)).toBoolean())
    return {
      verdict: 'halted',
      why: 'a fork witness is recorded: this client proved two conflicting segments from one head ' +
        'and will accept no further advance. Resolution is a NEW deployment at a new anchor.',
    };
  const c = canonicalBootstrapState(pins);
  const atGenesis =
    observed.turns.equals(Field(0)).toBoolean() &&
    observed.head.equals(c.head).toBoolean() &&
    observed.prevHead.equals(c.prevHead).toBoolean() &&
    observed.acceptedHistory.equals(c.acceptedHistory).toBoolean();
  if (atGenesis)
    return {
      verdict: 'genesis',
      why: "the account is at the genesis the verification key pins, and every head it ever holds " +
        'will have been reached by an accepted proof.',
    };
  return {
    verdict: 'operator-asserted-head',
    why:
      'the account is NOT at the pinned genesis, so its current head rests on the deployer\'s ' +
      'assertion as well as on the proofs since. That is the weak-subjectivity anchor; it is ' +
      'legitimate and it is not a proof.',
  };
}

// ===========================================================================
// 4. The seal — the same functions the chain emits it with.
// ===========================================================================

/**
 * `terminalDigest` — byte-for-byte `RootFriUniform`'s. Kept here as ONE exported
 * definition because the drift this repo has paid for is two sides computing
 * "the same" message differently (a signed `effects_hash` compared against
 * nothing; `terminalSeal` living twice at two arities).
 */
export const terminalDigest = (accOutDigest: Field, chainVkRoot: Field): Field =>
  Poseidon.hash([accOutDigest, chainVkRoot]);

/** The chain's closing seal, from the preimage a caller exhibits. */
export const terminalSealOf = (
  friCommit: Field,
  accOutDigest: Field,
  chainVkRoot: Field,
  totalSteps: number | Field,
): Field => taggedTerminalSeal(friCommit, terminalDigest(accOutDigest, chainVkRoot), totalSteps);

/** The out-of-circuit twin of the digest the chain feeds `terminalDigest`:
 *  `digestOfLanes([...acc.limbs, ...liveOut])`. Exported so a harness cannot
 *  build the preimage a second way. */
export const accOutDigestOf = (accLimbs: Field[], liveOut: Field[]): Field =>
  digestOfLanes([...accLimbs, ...liveOut]);

// ===========================================================================
// 5. The head, out of circuit — the twin the differential runs on.
// ===========================================================================

export type HeadState = {
  head: bigint;
  prevHead: bigint;
  turns: bigint;
  lastSegmentTurns: bigint;
  acceptedHistory: bigint;
  fork: bigint;
};

export type ClaimValues = {
  genesisRoot: bigint;
  finalRoot: bigint;
  numTurns: bigint;
  chainDigest: bigint;
};

/** The four claim fields, as circuit values. `ChainClaim` IS this shape, so the
 *  two functions below are called by the `@method` and by the twin without
 *  either side re-spelling the message. */
export type ClaimFields = {
  genesisRoot: Field;
  finalRoot: Field;
  numTurns: Field;
  chainDigest: Field;
};

export const claimFieldsOf = (c: ClaimValues): ClaimFields => ({
  genesisRoot: Field(c.genesisRoot),
  finalRoot: Field(c.finalRoot),
  numTurns: Field(c.numTurns),
  chainDigest: Field(c.chainDigest),
});

/**
 * The history link — the CLIENT'S OWN receipt chain over the claims it accepted.
 *
 * ⚑ THIS IS NOT dregg's `chainDigest` AND MUST NOT BE READ AS ONE. dregg folds
 * `acc = commit(l.acc ‖ r.acc)` through a BALANCED BINARY TREE over turns
 * (`ivc_turn_chain.rs: combine_seg`, `fold_host_segs_balanced`), so the
 * concatenation of two accepted segments has an `acc` this gate cannot
 * recompute — two accepted segments are siblings in that tree only by accident.
 * What this commits to is the ORDERED LIST OF SEGMENTS THIS CLIENT ACCEPTED,
 * which is a Mina-side artifact with a Mina-side meaning.
 *
 * ⚑ ONE DEFINITION, AND THE `@method` CALLS IT. Both sides of a message computed
 * twice is the failure this tree has already paid for (a signed `effects_hash`
 * compared against nothing; `terminalSeal` living twice at two arities), so this
 * is provable-typed and the circuit calls this exact function.
 */
export const historyLink = (prev: Field, c: ClaimFields): Field =>
  Poseidon.hash([HEAD_TAGS.history, prev, c.genesisRoot, c.finalRoot, c.numTurns, c.chainDigest]);

/** The fork witness, same discipline: one definition, called in circuit. */
export const forkWitnessOf = (c: ClaimFields): Field =>
  Poseidon.hash([HEAD_TAGS.fork, c.genesisRoot, c.finalRoot, c.numTurns, c.chainDigest]);

/**
 * **THE DECISION, out of circuit.** What a claim IS relative to a head — and it
 * is four-valued, because "refused" collapses three different findings.
 *
 *   `advance` — `G` is the head we hold. The head moves.
 *   `fork`    — `G` is the head the LAST accepted advance started from, the
 *               segment is the SAME LENGTH, and it ends somewhere else. Two
 *               different `N`-turn executions from one state: the state machine
 *               equivocated, and this client is done.
 *   `stale`   — `G` is neither. A perfectly honest replay of old history, a
 *               segment from a state we never held, or a proof about a different
 *               chain. Nothing happens; the client is not halted by it.
 *   `halted`  — a fork is already recorded. Nothing is accepted, ever again.
 *
 * ⚑ WHY `fork` REQUIRES THE SAME LENGTH. Without it, `(prevHead → X, 1 turn)`
 * and `(prevHead → Y, 3 turns)` collide as a "fork" when X is simply an
 * intermediate state on the way to Y — an honest PREFIX read as an equivocation,
 * and a one-transaction permanent halt anyone could trigger. With it, the two
 * segments are the same start, the same count and different ends, which a
 * deterministic state machine cannot produce from one turn sequence.
 *
 * ⚠ AND ITS WINDOW IS ONE ADVANCE DEEP. A fork at `head - 2` is `stale` here,
 * not `fork`: the gate holds `prevHead` and not the whole list of past heads.
 * Closing that needs an accumulator over accepted heads and a membership witness
 * in the fork report; it is named as the residual rather than implied away.
 */
export function decideBigInt(
  s: HeadState,
  c: ClaimValues,
): { verdict: 'advance' | 'fork' | 'stale' | 'halted'; why: string } {
  if (s.fork !== 0n) return { verdict: 'halted', why: 'a fork witness is already recorded' };
  if (c.numTurns === 0n) return { verdict: 'stale', why: 'a zero-turn segment moves nothing' };
  if (c.genesisRoot === s.head)
    return { verdict: 'advance', why: 'the segment starts at the head this client holds' };
  if (s.turns !== 0n && c.genesisRoot === s.prevHead && c.numTurns === s.lastSegmentTurns) {
    if (c.finalRoot === s.head)
      return { verdict: 'stale', why: 'this IS the segment already accepted, re-presented' };
    return {
      verdict: 'fork',
      why: 'same start, same turn count, a different end — the state machine equivocated',
    };
  }
  return { verdict: 'stale', why: 'the segment starts at a state this client does not hold' };
}

/** The state an accepted advance leaves behind. */
export function advanceBigInt(s: HeadState, c: ClaimValues): HeadState {
  const d = decideBigInt(s, c);
  if (d.verdict !== 'advance')
    throw new Error(`advanceBigInt was handed a '${d.verdict}' claim: ${d.why}`);
  return {
    head: c.finalRoot,
    prevHead: s.head,
    turns: s.turns + c.numTurns,
    lastSegmentTurns: c.numTurns,
    acceptedHistory: historyLink(Field(s.acceptedHistory), claimFieldsOf(c)).toBigInt(),
    fork: 0n,
  };
}

// ===========================================================================
// 6. The gate.
// ===========================================================================

let built: string | null = null;

/**
 * Build the head gate at a pin set.
 *
 * ⚑ A FACTORY BECAUSE THE PINS ARE IN THE VERIFICATION KEY. A `@state` pin is an
 * operator assertion written by a signature-authorized deploy — the
 * `placeholderRelay` shape, one indirection removed. A CIRCUIT pin makes the
 * deployed ADDRESS commit to which chain this account will accept, so rotating
 * dregg's key list rotates the address: a flag day you can see rather than a
 * state write you cannot.
 *
 * ⚑ ONE PIN SET PER PROCESS. o1js identifies a `SmartContract` by its class, and
 * two classes of one name in one process is the `DynamicProof.tag()` hazard
 * again. A second call with different pins throws rather than returning a class
 * whose identity depends on creation order.
 */
export type HeadGateOpts = {
  /** ⚑ FALSE builds the UNPINNED CONTROL — `vk.hash.assertEquals` removed and
   *  NOTHING else — so a refusal by the pinned gate is attributable to the pin
   *  rather than to the proof being malformed somewhere else. It is never
   *  deployed and never reported as if it verified anything. */
  pinVk?: boolean;
  /** ⚑ FALSE builds the UNSEALED CONTROL — the terminal-seal exhibition
   *  removed, and nothing else. Its whole job is to ACCEPT a mid-chain step
   *  boundary that the sealed gate refuses. */
  requireSeal?: boolean;
};

export function makeDreggHeadGate(rawPins: DreggChainPins, opts: HeadGateOpts = {}) {
  const pins = assertRealPins(rawPins);
  const pinVk = opts.pinVk !== false;
  const requireSeal = opts.requireSeal !== false;
  const fingerprint =
    `${pins.terminalVkHash}/${pins.chainVkRoot}/${pins.totalSteps}/${pins.genesisRoot}` +
    `/${pinVk}/${requireSeal}`;
  if (built !== null && built !== fingerprint)
    throw new Error(
      'a SECOND DreggHeadGate at DIFFERENT pins in one process: o1js identifies a contract by its ' +
        'class and both would be named `DreggHeadGate`. Build one gate per process.',
    );
  built = fingerprint;

  const TERMINAL_VK_HASH = Field(pins.terminalVkHash);
  const CHAIN_VK_ROOT = Field(pins.chainVkRoot);
  const TOTAL_STEPS = Field(pins.totalSteps);
  const GENESIS_ROOT = Field(pins.genesisRoot);

  /**
   * The obligation BOTH methods discharge, in ONE place: the proof verifies
   * under the pinned key, and its boundary is the chain's TERMINAL seal at the
   * pinned length under the pinned key list.
   *
   * ⚑ THE SECOND HALF IS NOT DECORATION. Without it the gate accepts a proof of
   * the same program at any query — a chain that walked SIX of nineteen queries
   * carrying the identical claim — because the last block position is ONE
   * program emitting `Provable.if(isQ[Q-1], seal, step)`.
   */
  function openTerminal(
    terminal: DreggTerminalProof,
    vk: VerificationKey,
    friCommit: Field,
    accOutDigest: Field,
  ): ChainClaim {
    if (pinVk)
      vk.hash.assertEquals(
        TERMINAL_VK_HASH,
        'DreggHeadGate: the proof was made under a key this gate does not name',
      );
    terminal.verify(vk);

    const po = terminal.publicOutput;
    if (requireSeal)
      terminalSealOf(friCommit, accOutDigest, CHAIN_VK_ROOT, TOTAL_STEPS).assertEquals(
        po.boundary,
        'DreggHeadGate: the boundary is not this chain\'s TERMINAL seal at the pinned length',
      );
    return po.claim;
  }

  class DreggHeadGate extends SmartContract {
    /** dregg's current state anchor as this client knows it: `packLanes(new8)`,
     *  248 of 254 bits of a BabyBear octet. `app_state_0`, so the daemon's
     *  precondition messages name it. */
    @state(Field) head = State<Field>();
    /** The head the LAST accepted advance started from — the only past head this
     *  client keeps, and therefore the only depth at which it can recognise an
     *  equivocation. */
    @state(Field) prevHead = State<Field>();
    /** Cumulative turns behind `head`, summed over accepted segments. */
    @state(Field) turns = State<Field>();
    /** `numTurns` of the last accepted segment. Kept so a fork report can
     *  require the SAME LENGTH and stop reading an honest prefix as a fork. */
    @state(Field) lastSegmentTurns = State<Field>();
    /** THIS CLIENT'S receipt chain over the claims it accepted — NOT dregg's
     *  `chainDigest`, which folds through a balanced tree this gate cannot
     *  reproduce. See `historyFoldBigInt`. */
    @state(Field) acceptedHistory = State<Field>();
    /** Zero, or the witness of a proved equivocation. Non-zero HALTS the client
     *  permanently: there is no `resolveFork`, and that is the design. */
    @state(Field) fork = State<Field>();

    /**
     * Deploying names the weak-subjectivity anchor. It is the ONE key act in
     * this contract's life and the type says so.
     *
     * ⚑ THE DEPLOY WRITES STATE AND THE DEPLOY IS SIGNATURE-AUTHORIZED. Nothing
     * here pretends otherwise. What the circuit adds is that the FIRST accepted
     * segment must start at `GENESIS_ROOT`, a compile-time constant — so a
     * deployer's `head` at `turns = 0` is not load-bearing, and a deployer who
     * wants to assert a LATER head has to write a non-zero `turns`, which
     * `bootstrapProvenance` reports as `operator-asserted-head`.
     */
    async deploy(props?: DeployArgs & { bootstrap?: DreggBootstrap }) {
      await super.deploy(props);
      const b = props?.bootstrap;
      if (b === undefined || b.provenance !== 'weak-subjectivity-anchor')
        throw new Error(
          'DreggHeadGate.deploy({ bootstrap }) requires a DreggBootstrap from ' +
            '`DreggBootstrap.weakSubjectivityAnchor(...)`. The first head has nothing before it ' +
            'and nothing can verify it; naming that is not optional.',
        );
      if (!b.genesisRoot.equals(GENESIS_ROOT).toBoolean())
        throw new Error(
          'the bootstrap anchor is not the genesis this gate\'s VERIFICATION KEY pins. Deploying ' +
            'it would build an account whose first advance can never be satisfied.',
        );
      const c = canonicalBootstrapState(pins);
      this.head.set(c.head);
      this.prevHead.set(c.prevHead);
      this.turns.set(c.turns);
      this.lastSegmentTurns.set(c.lastSegmentTurns);
      this.acceptedHistory.set(c.acceptedHistory);
      this.fork.set(c.fork);
    }

    /**
     * **THE ADVANCE.** Move the head because dregg's root proof said so.
     *
     * The extension relation is `claim.genesisRoot == head` — literally
     * `combine_seg`'s own continuity condition (`l.last_new8 == r.first_old8`),
     * lifted to the packed anchor. A segment that does not start where this
     * client stands is not an advance, and the refusal is a constraint failure
     * rather than a branch, so a caller cannot build the transaction at all.
     *
     * ⚑ REPLAY NEEDS NO COUNTER. After the advance `head == H`, so re-presenting
     * the same proof requires `G == H`, which is false for any segment that
     * moved the state. `getAndRequireEquals` also puts an `app_state`
     * precondition on the transaction, so two concurrent advances cannot both
     * apply. Said here rather than left to a comment implying a nonce.
     */
    @method async advanceHead(
      terminal: DreggTerminalProof,
      vk: VerificationKey,
      friCommit: Field,
      accOutDigest: Field,
    ) {
      const fork = this.fork.getAndRequireEquals();
      fork.assertEquals(Field(0), 'DreggHeadGate: this client is HALTED by a recorded fork');

      const claim = openTerminal(terminal, vk, friCommit, accOutDigest);

      const head = this.head.getAndRequireEquals();
      const turns = this.turns.getAndRequireEquals();
      const history = this.acceptedHistory.getAndRequireEquals();

      //  ⚑ THE BOOTSTRAP, IN THE CIRCUIT. The first segment must start at the
      //  pinned genesis whatever the deploy wrote; every later one must start at
      //  the head an accepted proof left.
      const first = turns.equals(Field(0));
      const mustStartAt = Provable.if(first, GENESIS_ROOT, head);
      claim.genesisRoot.assertEquals(
        mustStartAt,
        'DreggHeadGate: the segment does not start at this client\'s head',
      );

      //  A zero-turn segment would let `H != G` with nothing between them.
      //  `combine_seg` never emits one (leaves are count 1), so this refuses an
      //  object dregg does not build.
      claim.numTurns.assertNotEquals(Field(0));
      claim.finalRoot.assertNotEquals(Field(0));
      //  ⚑ CANONICITY IS INHERITED, AND SAYING WHERE FROM IS THE POINT. The 25
      //  lanes are `canonicalLane`-checked inside `readClaimLanes` and the seal
      //  binds them to `dagDigest`, so the packing is injective before this gate
      //  sees it. What is NOT inherited is that `turns` stays meaningful: it
      //  accumulates in a Pasta field, so it would take ~2^223 advances to wrap.

      this.prevHead.set(head);
      this.head.set(claim.finalRoot);
      this.turns.set(turns.add(claim.numTurns));
      this.lastSegmentTurns.set(claim.numTurns);
      this.acceptedHistory.set(historyLink(history, claim));
    }

    /**
     * **THE FORK.** A proof that the state machine equivocated where this client
     * already committed — same start, same turn count, a different end.
     *
     * ⚑ WHY A FORK IS A DECISION AND NOT AN OVERWRITE. A segment proof says `N`
     * turns are EXECUTABLE from `G` to `H`. It says nothing about which of
     * several executable futures dregg's consensus finalized — no committee, no
     * blocklace certificate rides in it. So a client that saw two of them and
     * PICKED one would be implementing first-come-wins, which is not dregg's
     * finality rule and would be a light client asserting a consensus answer it
     * does not have. This one stops instead, and records the evidence.
     *
     * ⚑ AND THERE IS NO `resolveFork`. Un-halting would be a key act, and the
     * whole point of this contract is that it has none after its bootstrap.
     * Resolution is a NEW deployment at a new weak-subjectivity anchor — a
     * visible flag day, with the halted account left on chain as the evidence
     * that it happened.
     *
     * ⚠ THE LIVENESS COST, STATED. One valid conflicting terminal proof halts
     * this client forever. That is 61 to 905 Pickles slices of work rather than
     * a cheap grief, and it is only reachable when dregg genuinely produced two
     * `N`-turn executions from one state — but it IS a permanent halt and the
     * operator has to redeploy.
     */
    @method async reportFork(
      terminal: DreggTerminalProof,
      vk: VerificationKey,
      friCommit: Field,
      accOutDigest: Field,
    ) {
      const fork = this.fork.getAndRequireEquals();
      fork.assertEquals(Field(0), 'DreggHeadGate: a fork witness is already recorded');

      const claim = openTerminal(terminal, vk, friCommit, accOutDigest);

      const head = this.head.getAndRequireEquals();
      const prevHead = this.prevHead.getAndRequireEquals();
      const turns = this.turns.getAndRequireEquals();
      const lastTurns = this.lastSegmentTurns.getAndRequireEquals();

      //  ⚑ A FRESH CLIENT CANNOT BE HALTED. At `turns == 0` the head IS the
      //  genesis and `prevHead` equals it, so every honest first segment would
      //  satisfy "starts at prevHead, ends elsewhere". Without this guard the
      //  first honest proof anyone produced would halt the client.
      turns.assertNotEquals(
        Field(0),
        'DreggHeadGate: nothing has been accepted yet, so nothing can conflict with it',
      );

      claim.genesisRoot.assertEquals(
        prevHead,
        'DreggHeadGate: a fork report must start where the last accepted segment started',
      );
      claim.numTurns.assertEquals(
        lastTurns,
        'DreggHeadGate: a fork report must be the SAME LENGTH — a different length is a prefix, ' +
          'not an equivocation',
      );
      claim.finalRoot.assertNotEquals(
        head,
        'DreggHeadGate: this is the segment already accepted, not a conflicting one',
      );

      this.fork.set(forkWitnessOf(claim));
    }
  }

  return {
    DreggHeadGate,
    pins,
    /** ⚑ CARRIED SO A TRANSCRIPT CANNOT READ A CONTROL AS THE GATE. Both false
     *  is not a gate; it is the object whose whole purpose is to accept. */
    pinVk,
    requireSeal,
    variant: pinVk && requireSeal ? 'GATE' : `CONTROL(${pinVk ? '' : 'UNPINNED '}${requireSeal ? '' : 'UNSEALED'})`.trim(),
    TERMINAL_VK_HASH,
    CHAIN_VK_ROOT,
    TOTAL_STEPS,
    GENESIS_ROOT,
  };
}

/** ⚑ TEST-ONLY. Lets one process build a second gate at different pins, which
 *  the factory otherwise refuses. Named for what it is so it cannot be mistaken
 *  for a reset the gate needs. */
export function __resetHeadGateFactoryForTest() {
  built = null;
}

// ===========================================================================
// 7. THE CUTOVER — what replaces `placeholderRelay`, when, and what then
//    refuses to load.
// ===========================================================================

/**
 * ⚑ WRITTEN DOWN RATHER THAN INTENDED, because the failure mode this repo has
 * paid for is a correct fix that gets deferred into a careful write-up and never
 * happens.
 *
 * The rule this obeys is the other one: **do not delete `placeholderRelay`
 * before the proof path works.** `DreggAttestedGate`'s anchor is gated by a
 * labelled key; deleting the key today under Mina's `editState: proof` makes
 * that anchor world-writable, which is strictly worse. So the two contracts
 * coexist, and the placeholder dies on a MEASURED event rather than on a
 * decision.
 *
 * ⚑ THE TRIGGER IS ONE OBSERVABLE THING: an `advanceHead` transaction included
 * on Devnet, against pins emitted by a real chain compile, consuming a real
 * terminal proof. Not "the gate compiles", not "the stand-in is accepted".
 */
export const PLACEHOLDER_CUTOVER = {
  phases: [
    {
      id: 'P1',
      what: 'DreggHeadGate is written and typechecks. Nothing on chain changes.',
      done: 'this file exists and `npm run typecheck` is green',
    },
    {
      id: 'P2',
      what:
        'the gate compiles; the stand-in table runs (vk pin, seal exhibition, extension, halt, ' +
        'fork) with an UNPINNED control that ACCEPTS what the pinned one refuses',
      done: '`npm run head-anchor` at MINA_TIER=1 prints its table with no NOT-ATTRIBUTABLE row ' +
        'except the real-terminal one',
    },
    {
      id: 'P3',
      what:
        'dregg\'s verification chain is compiled and `dregg-chain-pins.json` is emitted from that ' +
        'run — terminalVkHash, chainVkRoot, totalSteps, genesisRoot, all measured',
      done: '`assertRealPins` passes on a file no human typed, and the stand-in is REFUSED at the ' +
        'vk pin against those pins',
    },
    {
      id: 'P4',
      what: 'the chain is PROVED to a terminal proof and `advanceHead` consumes it on Devnet',
      done: 'an included transaction, recorded the way `devnet-deployment.json` records one',
      gate: 'ember — outward-facing, on chain, irreversible',
    },
    {
      id: 'P5',
      what:
        'placeholderRelay is DELETED: `DreggAttestedGate`, `setDreggRoot`, `placeholderAuthMessage`, ' +
        '`signPlaceholderAnchor`, `DreggAnchorStatement`, `proveAnchor`, the relay key in ' +
        '`devnet-common.ts` and `placeholderRelayAddress` in the deployment record all go',
      done: 'grep for `placeholderRelay` in this tree returns HORIZONLOG and docs only',
      refusesToLoad:
        'a key file carrying a relay key (invert `devnet-common.ts`\'s current check, which today ' +
        'refuses a file WITHOUT one); a deployment record carrying `placeholderRelayAddress`; the ' +
        'old zkApp address, which stops corresponding to any source in the tree',
    },
  ],
  /** ⚑ AND WHAT DOES NOT COME ALONG. `actOnAttestedLeaf` opens a leaf under a
   *  MINA-POSEIDON Pasta Merkle root; this gate's head is `packLanes(new8)`, a
   *  BabyBear state anchor. They are different objects and no rename makes them
   *  one. A leaf gate over the new head is a BabyBear-Poseidon2 membership proof
   *  (`Poseidon2Merkle.foldOpening`, which `DreggAnchorStatement` already runs)
   *  whose public input is the packed root — it is the named follow-up, and
   *  carrying `actOnAttestedLeaf` across unchanged would be the migration
   *  theater this repo forbids. */
  notCarriedAcross: 'actOnAttestedLeaf — the head changes hash family, so the leaf gate is rebuilt',
} as const;

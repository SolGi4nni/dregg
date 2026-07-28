# Richer on-chain clients of dregg: from a root-tracker to a state oracle

*Present-tense, what-is. The design for evolving dregg's EVM contracts from a bare
settlement-root tracker into RICHER clients — contracts that can QUERY dregg state, PROVE
facts about it, move value IN and OUT, and REACT to dregg effects. This lands directly on
tokenized-RWA / DeFi chains (Robinhood Chain, Base): a chain where value already lives can
gate entitlements, honor withdrawals, and settle instructions on a **proof** of dregg state
rather than a bridge vote.*

> ## ⚑ SUPERSEDED IN PART — 2026-07-28
>
> **Rungs 1 (sub-root history) and 2 (inclusion-proof verification) as described below
> were BUILT AND HAVE BEEN DELETED.** `DreggStateOracle.recordEpoch(stateRoot, height,
> subRootVec)` wrote the four keccak mirror sub-roots and the epoch height straight to
> storage with only `isProvenRoot(stateRoot)` checked, and `proveHolding` /
> `proveNullifierSpent` / `proveCommitmentExists` / `verifyAgainstSubRoot` served
> inclusion proofs against them. The keccak check is sound *given the sub-root*, so the
> entire surface inherited the recorder's word: a compromised recorder could publish a
> sub-root it built itself and forge any holding, any spend, any note commitment.
>
> The document below repeatedly calls this "operator-attested until the exposure weld
> lands". That is an accurate description of a hole, and it sat for weeks with consumers
> invited to build on it (`proveHolding` is described as what a lending market gates on).
> Per `CLAUDE.md` it is fixed rather than documented:
>
> - **height** is now PROOF-BOUND: `DreggSettlement` records the cumulative proven height
>   per proven root and `IDreggSettlement.provenHeightOf` serves it. Nothing attests it.
> - **the sub-roots and every reader of them are GONE**, following `DreggSettlement`'s own
>   precedent for the operator-attested `outboundMessageRoot`.
> - **the recorder role is GONE**: with nothing left to attest, `recordEpoch` is
>   permissionless.
>
> What survives is an ordered, proof-bound index of settled roots plus the eth->dregg
> instruction channel. Rungs 3-5 below compose against rung 2 and are therefore **blocked
> on the same weld**, not buildable now.
>
> ⚠ **The weld is a LEAN-AUTHORED CIRCUIT CHANGE, and the description below understates
> it.** Exposing the Poseidon2 sub-roots as public inputs is NOT sufficient: what this
> contract served were KECCAK MIRRORS — a different tree over the same set under a
> different hash — and no EVM contract can relate a Poseidon2 field root to a keccak
> Merkle root. Binding them requires the CIRCUIT to build the keccak mirror and prove it
> agrees with the committed set (keccak-in-circuit over the four sets), then expose the
> commitment as extra apex claim lanes (25 -> 33 public inputs, a new Groth16 VK and hence
> a new `VK_DIGEST` on all three chains). That work belongs in `metatheory/`, with the
> Rust emit path following; the exact obligation is written out in the contract header of
> `chain/contracts/DreggStateOracle.sol`.
>
> Read the rest of this document as the DESIGN INTENT, not as what is deployed.

## Where we start (the bare client)

`chain/contracts/DreggSettlement.sol` verifies a Groth16(BN254) proof wrapping dregg's
recursive STARK (`circuit-prove/src/ivc_turn_chain.rs`) and advances a single proven state
root. Its whole surface is the **25-lane public-input contract** (`IDreggSettlement.sol`):

```
[0..8)   genesis_root   [BabyBear; 8]
[8..16)  final_root     [BabyBear; 8]     ← the settled dregg STATE root
[16]     num_turns
[17..25) chain_digest   [BabyBear; 8]
```

`final_root` is dregg's Poseidon2 state commitment `recStateCommit`
(`metatheory Dregg2/Circuit/StateCommit.lean`), keccak-packed to a `bytes32` on-chain
(`packLanes`). That root **binds the whole dregg state** — including, via `restHash`
(`RestHashIffFrame`, StateCommit.lean:243-254), the sub-roots `nullifierRoot`, `revokedRoot`,
`commitmentsRoot`, and the `heaps`. The bare client answers exactly one question:
*"is root R proven?"* (`isProvenRoot`). No contract can yet ask *"what is IN R?"*.

That is the gap this design closes.

## The ladder (bare → full)

Each rung names the dregg state it reads, whether it is buildable now or needs a weld, and
its trust grade.

| # | Component | dregg state it reads | Build effort | Trust grade |
|---|---|---|---|---|
| 1 | **Epoch + sub-root history** | settled `final_root` history + exposed sub-roots (`nullifierRoot`/`commitmentsRoot`/`balanceRoot`/`heapRoot`, StateCommit `restHash`) | **Buildable now** (state root binding); sub-root *trustlessness* needs the exposure weld | State root = proof-bound (`isProvenRoot`). Sub-roots = operator-attested until exposed as PIs. |
| 2 | **Inclusion-proof verification** ⭐ | any sub-root (nullifier / commitments / balance / heap) | **Buildable now** (prototyped here) | **SOUND** given the sub-root — keccak collision-resistance; a forged leaf/path cannot reach the root. |
| 3 | **Inbound messages / deposits** (eth → dregg) | none read; EMITS a commitment dregg ingests | **Buildable now** | Standard relayer/light-client trust (dregg watches the log). Value custody via escrow (#5). |
| 4 | **Outbound messages / effects** (dregg → eth) | the **outbound message root** (the 26th-PI, currently fail-closed) | **Needs a weld** (the message-root binding) | Would be proof-bound *after* the weld. Fail-closed today. |
| 5 | **Deposit / withdraw escrow** (value in/out) | balance / commitments sub-root (composes #2) | **Buildable now** (composes #2 + a settled sub-root) | Sound withdrawal given an exposed balance/commitments sub-root; = #2's grade. |

### Rung 1 — Epoch + sub-root history

`DreggSettlement` already keeps a *set* of proven roots (`_provenRoots`) for reorg-safety —
a cross-chain message proven under a since-superseded root must still verify. The richer
client extends this from "the top state root" to "the top state root **and its sub-roots**",
keyed by epoch. `DreggStateOracle.recordEpoch(stateRoot, height, subRootVec)` stores, per
settled root, the four sub-roots `[Balance, Nullifier, Commitments, Heap]`, and enumerates
epochs (`epochRoots`, `epochCount`).

The dregg state it reads: the sub-roots the state commitment binds — `nullifierRoot`,
`revokedRoot`, `commitmentsRoot`, `heaps` are literally the fields `RestHashIffFrame` hashes
into the state root (StateCommit.lean:253). The **balance root** is the Merkle image of the
per-cell balance leaves inside `cellDigest`.

**Honest trust boundary.** The sub-roots are *cryptographically committed* by the settled
Poseidon2 state root, but they are not *extractable on-chain cheaply*: opening the state root
into `restHash` + the sub-roots would require Poseidon2-over-BabyBear in the EVM (heavy). So
today the sub-roots are recorded by an authorized `recorder` and are only as trustworthy as
that recorder — **the same class of trust hole the outbound message root has** (see rung 4).
The one binding enforced now: `recordEpoch` reverts unless `settlement.isProvenRoot(stateRoot)`,
so no epoch can ride a state dregg never settled. Making the sub-roots trustless is the
**sub-root exposure weld**: thread each sub-root through the fold's segment accumulator, expose
it as apex claim lanes (`expose_claim`), bind those lanes in the shrink + gnark
`SettlementCircuit`, mint a new VK — after which `settle` records sub-roots it can CHECK against
the proof's PIs. This is precedented at the turn level: `circuit/src/effect_vm_descriptors.rs`
(:2745, :2759) already PI-binds each per-turn nullifier/commitment insert; the weld is
aggregating those to a per-span sub-root at the apex.

### Rung 2 — Inclusion-proof verification (THE highest-value first component)

A pure function: *"leaf X is in dregg sub-root R (of settled epoch S)."* This is what makes
the client usable — any EVM contract can now prove a dregg fact on-chain:

- `proveHolding(stateRoot, account, balance, index, siblings)` — "address A holds `balance` in
  dregg" (an RWA/DeFi contract gates entitlements on it; "A holds ≥ N" by proving A's exact
  balance leaf and comparing).
- `proveNullifierSpent(stateRoot, nullifier, …)` — "this note is spent" (double-spend / replay
  guard for a market or bridge).
- `proveCommitmentExists(stateRoot, commitment, …)` — "this note exists".
- `verifyAgainstSubRoot(stateRoot, kind, leaf, index, siblings)` — the generic primitive.

**Why Merkle and not the poly-eval accumulator.** dregg's real O(1) membership tool is the
poly-eval accumulator over BabyBear⁴ (`commit/src/accumulator.rs`, `Acc = ∏(α − hᵢ)`). It is
the right tool **in-circuit or for a set-holding verifier**, but it is **setless-forgeable**,
so it is *not* an on-chain verifier: over a field, for any target `x ≠ α` an attacker picks
`quotient = Acc·(α−x)⁻¹` (membership) or any nonzero `remainder'` with the matching quotient
(non-membership) and the identity `quotient·(α−x)[+remainder] == Acc` passes — even for a
non-member. This is documented in that file's "Soundness scope" note and closed only by
`verify_non_membership_bound`, which **recomputes f(x) from the set** (a luxury an EVM contract
does not have). A Merkle root, by contrast, binds every leaf with only the root: each internal
node `keccak(left ++ right)` is collision-resistant on both children, so a forged leaf/path
cannot reach the root. **The accumulator path** (for a future O(1) on-chain non-membership) is a
KZG/pairing-based vector commitment — a separate, heavier build; named, not taken here.

**Poseidon2 vs keccak.** dregg's sub-roots are Poseidon2-over-BabyBear. Verifying inclusion
under the *native* Poseidon2 root on-chain needs a Poseidon2 EVM implementation (heavy but
finite). The EVM-cheap, EVM-sound choice is a **keccak MIRROR** of the sub-root — dregg
publishes a keccak Merkle tree over the same leaf set, exactly the construction already chosen
for the outbound message root (`DreggSettlement.sol`:32-51 — "an EVM-friendly (keccak)
commitment DISTINCT from the dregg STATE root"). The prototype verifies against the keccak
mirror; the Poseidon2-native path is named.

### Rung 3 — Inbound messages / deposits (eth → dregg)

`submitInbound(commitment, payload)` emits `InboundCommitment`; dregg's relayer/light-client
watches the log and mirrors the commitment into state (the inbound leg of
`docs/deos/INTERCHAIN-MODEL.md`). On its own it carries instructions/commitments; value custody
is a companion escrow (rung 5) that calls it on deposit. Buildable now; standard relayer trust
(dregg observes the chain — the same posture as any inbound light-client).

### Rung 4 — Outbound messages / effects (dregg → eth) — NEEDS THE WELD

A dregg turn triggering an on-chain action (release funds, mint, call a contract) requires
verifying a **dregg-proven outbound message** against the **outbound message root**. This is the
26th-PI work, and it is **fail-closed today** (`DreggSettlement.isProvenMessageRoot` returns
false for every input; `settle` reverts on any non-zero `outboundMessageRoot`). The turn already
commits its emitted effects (the 4-felt Poseidon2 effects-tree hash at descriptor PI
`EFFECTS_HASH`), but that commitment is **not threaded into the apex claim** — so there is
nothing proof-bound to check a submitted message root against, and recording an operator-supplied
root would be a forgeable trust hole. **The named weld** (verbatim from the bare client's residual
note): the fold's segment accumulator must absorb a per-turn outbound-message commitment; the apex
must expose it as claim lanes; the shrink + gnark `SettlementCircuit` must bind those lanes as
extra PIs (a new VK); then the contract checks `outboundMessageRoot` against the proof. This is the
**same weld** as rung 1's sub-root exposure — one fold-plumbing + VK-regen effort unlocks both #1's
trustless sub-roots and #4's outbound effects.

### Rung 5 — Deposit / withdraw escrow (value in/out)

The non-custodial value bridge: an escrow that HOLDS ERC-20/ETH and honors a withdrawal proven
by a dregg **inclusion proof** (compose rung 2 against an exposed balance/commitments sub-root,
plus a spent-nullifier guard). This is the shape `DreggVault.sol` already sketches (a note tree +
nullifier set + root-history grace window), upgraded from an SP1 proof envelope to the
oracle's Merkle inclusion against a settled dregg sub-root. Buildable now once the balance/
commitments sub-root is recorded; its soundness = rung 2's grade.

## What this prototype ships

- **`chain/contracts/DreggMerkle.sol`** — the EVM-sound positional keccak Merkle inclusion
  verifier (the reusable core), with the honest accumulator contrast in its header.
- **`chain/contracts/DreggStateOracle.sol`** — the richer client: epoch + sub-root history
  (rung 1), inclusion-proof verification (rung 2, the star), and the inbound commitment channel
  (rung 3). Reads `DreggSettlement` through `IDreggSettlement` only — additive, adds no trust to
  the settlement path.
- **`chain/test/DreggStateOracle.t.sol`** — a Foundry test that builds a REAL positional keccak
  Merkle tree over genuine dregg nullifier elements, records a proven epoch, and checks BOTH
  polarities: a genuine nullifier inclusion **verifies**; a forged nullifier, a tampered sibling,
  a wrong index, and a wrong sub-root kind all **reject**. 10/10 green (`forge test`).

## How this makes dregg's on-chain presence holistic

The bare client let a chain **verify that dregg settled**. The richer client lets a chain
**use what dregg settled**: an RWA vault gates a real-world-asset entitlement on
`proveHolding`; a lending market checks `proveNullifierSpent` before honoring a redemption;
a deposit contract feeds instructions in via `submitInbound`; an escrow releases value on an
inclusion proof (rung 5); and — after the one message-root weld — a dregg turn drives an
on-chain effect (rung 4). Query, prove, transact, react: the four verbs of an on-chain client,
each grounded in a proof the chain checks itself, no bridge validators. On a chain where value
already lives, that is the difference between "dregg exists over there" and "dregg is a
first-class settlement counterparty here."

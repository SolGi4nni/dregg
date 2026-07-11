# Interchain Adapters: dregg as a proof-carrying interoperability backend

*Draft — 2026-07-11. Companion to `docs/deos/LAYERZERO-CONCEPT-MAP.md` and
`docs/FINDING-chain-participation-census.md`. The Lean-modeling and code sections
are filled in from the in-tree audit; this file is the design frame.*

## The thesis

dregg does not need to pick one interop standard. Every cross-chain standard is,
underneath, a way to answer one question — **"did event E really happen on chain
C?"** — under some trust model. dregg already produces a succinct validity proof
of its own state transitions (`WholeChainProof`, verified by
`lightclient::verify_history`). So dregg's native role in any interop standard is
the **verification backend**: the thing that answers "did E happen" by *proof*
rather than by committee vote or optimistic assumption.

Rather than reimplement Tendermint / GRANDPA / Ethereum consensus inside our own
formal proofs, we **model the interaction**: an `InterchainAdapter` names, for
each standard, (1) what dregg checks in-circuit or on-chain, and (2) what it
*assumes* about the foreign chain — and a single soundness theorem is
parameterized over that assumption. Where we build a real light client (ETH
sync-committee, Solana Tower-BFT — already real in Rust), the assumption
discharges to a theorem; where in-circuit verification is foreclosed (Midnight),
the assumption is carried by an optimistic + 1-of-N watchtower, which dregg's
proof *makes objective*. This is the same shape as ember's bar: **be a full
client where you can, fall back to optimistic-with-proof-as-evidence where you
can't, never a blind committee wrap.**

## The trust-model lattice (every standard is one of these)

Ordered from strongest to weakest; the adapter tags each integration with its rung.

1. **Proof / light-client** — verify the foreign chain's consensus + a state
   inclusion proof. Trust = the foreign chain's own security + our verifier's
   correctness. Family: IBC (Tendermint light client), zk-light-clients
   (Succinct/Telepathy, Polymer, Electron, Lagrange), zkIBC.
   *dregg fit:* build the light client; this is the bar. Solana Tower-BFT already
   real in Rust (off-circuit); ETH sync-committee is the easiest unbuilt win.
2. **Optimistic + fraud proof** — assume valid, allow a bonded challenge within a
   window; 1 honest watcher suffices. Family: **Optics (Celo) → Nomad →
   Hyperlane** optimistic ISM, Across intents.
   *dregg fit:* ALREADY BUILT for Midnight (`Watchtower::examine`); dregg's STARK
   is the objective fraud-proof evidence, turning 2/3-committee trust into 1-of-N.
   This is the *strongest available* posture for any chain we can't yet
   light-client, and it is exactly the design ember worked on at Celo.
3. **Threshold / committee attestation** — an M-of-N set signs "E happened."
   Trust = honest majority of a permissioned set. Family: LayerZero DVNs,
   Wormhole guardians, Axelar validators, CCIP DON.
   *dregg fit:* the fallback of last resort (the SPL mirror's lock oracle is here
   today). Where a standard lets us register a **custom verifier** (LayerZero
   permissionless DVN, Hyperlane custom ISM, Axelar Interchain Amplifier), dregg
   plugs in as *one* verifier whose vote is backed by a real proof — upgrading the
   committee's weakest link.
4. **RPC / finality-tag trust** — trust a node's `finalized` tag or N
   confirmations. Not a real interop trust model; the current ETH/Base inbound
   listener sits here and must be lifted to rung 1 or 2.

## The standards, and where dregg's proof plugs in (2026 survey)

Every committee-default standard *also* exposes a seam to slot a cryptographic
verifier in — that seam is the whole opportunity. Ranked by fit for a
proof-carrying system:

| Standard | Default trust | The verifier seam | Permissionless? | dregg fit |
|---|---|---|---|---|
| **Hyperlane ISM** (ex-Celo/Optics team) | per-app modular (multisig default) | `IInterchainSecurityModule.verify(metadata, message)` — 2 fns, `verify` is non-view (stateful: verify one epoch proof, cheap lookups after) | **YES** — per-recipient opt-in, no governance; `CCIP_READ` moduleType routes arbitrary proof metadata w/ zero relayer changes; `POLYMER=12` enum precedent | **FLAGSHIP.** `DreggProofISM.verify` = dregg settlement proof attests the message. The default-path zk-ISM slot is UNCLAIMED. Directly continues the Optics work. |
| **LayerZero DVN** | X-of-Y-of-N committee | on-chain DVN adapter verifies your proof → `ReceiveUln302.verify(header, payloadHash, confirmations)` | **YES** — 77 DVN providers live; Polyhedra/Lagrange already do the zk-adapter pattern | **FASTEST DEMO.** dregg as a *required* DVN = conjunctive AND factor. Distribution (OApps configuring us) is the real work. |
| **IBC 08-wasm client** | Tendermint light client (cryptographic) | a CosmWasm `ClientState`/`ConsensusState` impl of ICS-02 (`verifyClientMessage`, `verifyMembership`, `checkForMisbehaviour`) | governance store per-counterparty (sanctioned, not open) | **DEEPEST.** `ClientState` pins dregg's circuit vkey; `VerifyClientMessage` runs `verify_history`. IBC Eureka already ships `SP1ICS07Tendermint.sol` (Tendermint-in-SP1 → Groth16) — our exact shape. CAVEAT: must solve fork-choice (validity ≠ canonicity) + reciprocal client hosting. |
| **OIF / ERC-7683 intents** | optimistic (Across) / agnostic | conforming `IInputOracle`/`hasAttested` proof verifier; the new (2026-05) `Witness` variable role is a first-class proof slot | **YES** — OIF default settlement is *already Hyperlane ISM-based* | dregg as the "the fill happened" settlement oracle; replaces the optimistic window with a validity proof. |
| **Wormhole NTT transceiver** | 13-of-19 guardians | app-layer custom transceiver verifies your proof, deployer sets M-of-N | open contract, **app-layer only** (core VAA path closed) | conjunctive 2/2 w/ guardians (Boundless/RISC0 precedent, live Aug 2025). Not transport-level. |
| **Axelar Amplifier** | PoS validators (47) | 3 CosmWasm contracts (Verifier/Gateway/Prover) on Axelar | governance + 50k AXL bond (gated) | substitutes committee on ingress, but egress still flows through the prover multisig. Deepest but slowest. |
| **Chainlink CCIP** | permissioned DON | — (OffRamp accepts one DON-signed path; RMN blessing now dormant) | **NO seam** | app-level self-verify inside `ccipReceive` only. |

**THE NOMAD LAW (hard design constraint on every `verify()` we ship).** Nomad's
$190M hack was a vacuity bug: a proxy init set `confirmAt[0x00]=1`, so every
*unproven* message (whose stored proof defaulted to `0x00`) verified as accepted —
"unproven maps to an accepted value." Every dregg ISM/DVN/client `verify` MUST be
proven to REJECT on the zero/default/⊥ input, with a test of that polarity. This
is the same discipline as [[feedback-dont-launder-vacuity-as-honest]] — a spec
must be false on the empty witness — and dregg's fail-closed default. It is the
single most important property of the outbound integrations.

## dregg's two directions

- **Outbound (dregg → chain C): dregg is the prover.** A foreign chain's security
  module / verifier contract consumes dregg's proof. Integration = implement the
  standard's verifier interface (e.g. a Hyperlane ISM, a LayerZero DVN adapter, an
  IBC client-state) whose `verify` calls dregg's on-chain settlement verifier
  (`DreggSettlement`, the 25-lane Groth16 check). One integration per standard's
  *verifier seam*, all resting on the same wrap prover.
- **Inbound (chain C → dregg): dregg is the verifier.** dregg checks C's finality
  before crediting state. Integration = a light client (rung 1) or a watchtower
  (rung 2) per chain, every one routing its mint through the committed
  consume-once nullifier gate (the double-mint fix on record in
  `BRIDGE-ARCHITECTURE-SOUNDNESS.md`).

## The permissionless seams worth targeting first

The high-value integration points are standards that expose a **bring-your-own-
verifier** seam, because dregg plugs in without anyone's permission:

- **Hyperlane ISM** (the Celo/Optics lineage) — a contract implementing the
  `InterchainSecurityModule` interface decides whether to accept a message. dregg
  provides a `DreggProofISM`: accept iff a dregg settlement proof attests the
  message. This is the flagship — it directly continues ember's Optics work and is
  optimistic-or-proof at our choosing.
- **LayerZero permissionless DVN** — register dregg as a DVN in an app's X-of-Y-of-N
  stack; dregg's vote is proof-backed.
- **Axelar Interchain Amplifier** — register a custom verifier for a new chain
  connection.
- **ERC-7683 cross-chain intents** — dregg as the settlement-correctness oracle for
  intent fills.

## What to extend (grounded in the in-tree audit) — do NOT invent a parallel shape

**Rust — the trust dials already exist; unify them, don't replace them.** There
is no `InterchainAdapter` trait yet, but every piece is present:
- Trust-tier enums, one per lane, all collapsing to the `consensus_verified: bool`
  the mint gate reads: `LockProofTrust::{StructureOnly, ConsensusVerified}`
  (`bridge/src/solana_trustless.rs:202`), `SnarkSystem::{Groth16Bn254, PlonkBn254,
  BindingOnly}` (`bridge/src/ethereum.rs:107`), the optimistic `Verdict::Fraud`
  from `Watchtower::examine` (`bridge/src/midnight_gateway.rs:230`), and
  `FinalizedAttestation` committee quorum (`lightclient/src/lib.rs:598`).
- `trait ProofVerifier` (`bridge/src/verifier.rs:111`) is the verification seam to
  add a foreign-ISM impl to; the RPC-transport trait family (`EthRpc`,
  `SolanaRpc`, `MinaRpc`, `SubstrateRpcClient`) is the observation seam.
- `PortableActionBinding {nullifier, recipient, destination_federation, amount}`
  (`bridge/src/action_binding.rs:78`) is the canonical full-fidelity cross-chain
  payload the adapter carries.
- **The single mint authority every inbound path already routes through:**
  `TurnExecutor::bridge_mint_against_lock` (`turn/src/executor/bridge_ledger.rs:261`)
  — trust gate (`TrustTooLow` if `!consensus_verified`), committed consume-once
  `lock_nullifier` against the same `note_nullifiers` set `NoteSpend` rides
  (double-mint fix), conservation backstop. A new adapter feeds THIS; it is the
  shared hypothesis, not a per-adapter concern.

So the Rust `InterchainAdapter` is a trait these relayers implement whose
associated attestation is one of the tiers above → `consensus_verified` (or a
richer rung) → `bridge_mint_against_lock`, carrying a `PortableActionBinding`.

**Lean — the "assume foreign chain finalized X ⟹ dregg mint sound" theorem
ALREADY EXISTS as the §8 CryptoPortal hypothesis.** Extend these, in order:
- `metatheory/Metatheory/SettlementSoundness.lean`: `SettlePred` (`:127`),
  `BindsLiveAuthority` (`:137`, a TYPED hypothesis never an axiom), keystone
  `settlement_soundness` (`:153`), the non-tautological `deployedSettle` (`:289`)
  + `deployedSettle_binds_live_authority` (`:305`), and the vacuity tooth
  `branchSettle_NOT_binds` (`:408`). A foreign-finality settlement is a NEW
  `SettlePred` we prove inhabits `BindsLiveAuthority`.
- `metatheory/Dregg2/Circuit/Spec/bridgeinboundmint.lean`: the §8 CryptoPortal
  hypothesis IS `foreignFinal` — "the other-chain confirmation governs WHEN the
  bridge may move; conservation holds regardless." Reuse `InboundMintSpec`,
  `execBridgeMintA_iff_spec`, and especially `bridgeMint_supply_delta` (a committed
  inbound mint leaves every asset's supply exactly unchanged — the negative-capable
  well absorbs the bridged supply) + the forgery-rejection `bridgeMint_rejects_*`.
  The foreign confirmation enters as a `Prop`-carrier (the `portalStep` pattern,
  `metatheory/Dregg2/Exec/Handlers/Bridge.lean:11`).
- The double-spend gate's Lean twin: `noteSpend_no_double_spend`
  (`metatheory/Dregg2/Exec/EffectsPaired.lean`) + the accumulator bridge
  (`NullifierAccumulatorKernelBridge.lean`).

So the Lean `InterchainAdapter` is a structure carrying
`foreignFinal : ForeignHeader → Prop` (= the §8 CryptoPortal `Prop`-carrier: an
assumed oracle for committee/optimistic rungs, a discharged theorem for
light-client rungs like the Solana stake-verified path) + `inclusion` + a
`TrustRung`, with the top theorem an instance of `settlement_soundness` /
`execBridgeMintA_iff_spec` parameterized over the adapter — each chain discharges
its own `foreignFinal` at its rung and inherits credit-soundness + conservation.

## Recommended build order

Grounded in "permissionless seam × shipped precedent × continues existing dregg work":

1. **Lean `InterchainAdapter` first** — the abstraction is the through-line and it
   already has a home. A structure over `foreignFinal`/`inclusion`/`TrustRung`
   instantiating `SettlePred`+`BindsLiveAuthority` and the §8 CryptoPortal
   `bridgeinboundmint` shape, with the four in-tree tiers
   (`LockProofTrust`/`SnarkSystem`/`Verdict`/`FinalizedAttestation`) as its rung
   variants. This is model-work, no foreign chain reimplemented — exactly ember's ask.
2. **Hyperlane `DreggProofISM.sol`** (the Optics-lineage flagship) — a
   two-function ISM whose `verify()` calls `DreggSettlement`'s 25-lane Groth16
   check, AND-ed with a message-id check via an Aggregation ISM (anti-replay).
   THE NOMAD LAW is a hard gate: a test proving `verify` reverts on the
   zero/default input. Routed via `CCIP_READ` moduleType so no relayer change is
   needed. Outbound (dregg is the prover).
3. **LayerZero `DreggDVN` adapter** — the fastest live demo; an on-chain DVN
   adapter verifying the same settlement proof, registerable permissionlessly as a
   required DVN. Shares the verifier contract with lane 2.
4. **ETH sync-committee inbound light client** (rung 1) — the easiest unbuilt
   full-client win (no BLS12-381 aggregate verify exists in-tree yet); lifts the
   ETH/Base listener off RPC-trust; routes its mint through
   `bridge_mint_against_lock`. Uses the Solana weak-subjectivity/stake-rotation
   code as the template. Inbound (dregg is the verifier).
5. **IBC 08-wasm client** (later, deepest) — a CosmWasm ICS-02 client pinning
   dregg's vkey; needs the fork-choice/misbehaviour story (validity ≠ canonicity)
   that lanes 1–4 don't. Sanctioned per-counterparty, not a quick plug-in.

Each outbound lane (2, 3, 5-outbound) rests on the SAME wrap prover
(`docs/deos/ETH-NATIVE-WRAP.md`) and the SAME `DreggSettlement` verifier — one
crypto core, many standard-shaped adapters. Each inbound lane routes through the
one committed consume-once mint gate.

## Non-goals

- Not reimplementing foreign consensus inside dregg's formal proofs (we model the
  *interaction* + assumption, discharging to a real light client only where we
  build one).
- Not a new bridge token or wrapped-asset custody model (assets stay in the
  shielded pool; see LAYERZERO-CONCEPT-MAP.md — no bridge wallet to vote/settle).

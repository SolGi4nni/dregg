# The Protocol Frontier For Apps — what dregg supports that apps only touch aspirationally

> **As-of census (~2026-06-27), partially executed since.** This is a point-in-time
> snapshot. Its chosen flagship — a real `SealedEscrow` atomic swap — has since
> **LANDED** (`demo/tests/sealed_escrow_atomic_swap.rs`), and `escrow-market` itself
> was regrounded onto the proven capacity (`SealedEscrowMarket`). Those two rows are
> flipped below; the rest of the spine (Vault/Membrane/StandingObligation UNUSED,
> conditional/eventual/promises UNUSED, no app implements a RingTradeParticipant)
> still holds. Re-census before treating any single row as live state.

dregg's substrate has grown far richer than its example apps exercise. This is a
pillar-by-pillar census of the *rich primitives that exist* (proven and wired)
against *which app actually uses them* (file:line), so we can see the aspirational
frontier clearly and pick the most inspiring Houyhnhnm-computing demonstrations to
build next.

"Houyhnhnm computing" (see [[DISTRIBUTED-HOUYHNHNM-FRONTIER]] / `HOUYHNHNM-CONVERGENCE.md`)
is the lens: a substrate is inspiring to the degree it demonstrates computation
that is **distributed · reversible · capability-secure · witnessed ·
content-addressed · persistent · branch-and-stitch**. We rank the frontier by how
vividly each pillar shows that vision when a *real app* drives it end to end.

The headline finding: **the kernel is years ahead of the demos.** Most of the
proven capacities have zero app users; apps overwhelmingly model everything as flat
`Effect::SetField` slots with hand-rolled caveats, re-deriving (and sometimes
faking) capacities the protocol already proves correct.

---

## The census — pillar by pillar

Legend: **USED** (a real app calls the real API) · **FAKED** (an app re-implements
the capacity with generic slots instead of the proven API) · **UNUSED** (no app).

### 1. House capacities (the six proven Track-2 cells)

`cell/src/{escrow_sealed,vault,membrane,obligation_standing,derived,factory}.rs`,
proven in `metatheory/Dregg2/Deos/{SealedEscrow,Vault,Membrane,StandingObligation,DerivedCell,Hatchery}.lean`.

| Capacity | API surface | App usage | Verdict |
|---|---|---|---|
| **SealedEscrow** | `open_escrow`/`deposit_leg`/`settle`/`reclaim_leg`/`check_claim` (`cell/src/escrow_sealed.rs:375,391,580,595,503`) | **regrounded** — `starbridge-apps/escrow-market/src/lib.rs` now drives the proven capacity via `SealedEscrowMarket` (`:180`), re-exporting `dregg_cell::escrow_sealed`; the old slot-caveat lifecycle is RETAINED only for out-of-scope dependents and is no longer the app's headline escrow (`:38-46`). Also the flagship `demo/tests/sealed_escrow_atomic_swap.rs`. | **USED** |
| **Vault** (conditional timelock) | `open_vault`/`claim`, `VaultTerms`/`Condition` (`cell/src/vault.rs`) | none | **UNUSED** |
| **Membrane** (forwarder / upward authority `meet`) | `Membrane`/`SealedMembrane`/`exercise`/`seal` (`cell/src/membrane.rs`) | none | **UNUSED** |
| **StandingObligation** (recurring discharge) | `open_obligation`/`discharge`, `ObligationTerms` (`cell/src/obligation_standing.rs`) | none | **UNUSED** |
| **DerivedCell** (committed aggregate over sources) | `bind_derivation`/`verify_derivation`, `DerivationSpec` (`cell/src/derived.rs`) | `starbridge-apps/supply-chain-provenance/src/derived.rs:47,111-138` | **USED** |
| **Hatchery** (object factory / EROS-style minting) | `FactoryDescriptor`/`CapTemplate`/`ChildVkStrategy` (`cell/src/factory.rs`) | `starbridge-apps/polis/src/lib.rs:114,303-315,1184` + framework re-exports (208 sites) | **USED** |

Three of the six proven capacities (Vault, Membrane, StandingObligation) still have
**zero** app users. The escrow gap this census originally flagged as its most glaring
fake — `escrow-market` re-implementing escrow by hand — has since been **closed**:
the app was regrounded onto the proven `SealedEscrow` capacity (`SealedEscrowMarket`),
and a disjoint flagship demo (`demo/tests/sealed_escrow_atomic_swap.rs`) drives the
`cell` API end to end. See the flagship section below (now landed).

### 2. umem cell-heaps (per-cell committed witnessed memory)

`cell/src/state.rs:198-224,827-860` (`heap_root`, `heap_map`, `get_heap`/`set_heap`),
`turn/src/umem.rs` (the openable umem projection / cross-cell heap reads).

- **USED** only by `dregg-doc/src/doc_heap.rs:109` (`DocHeapCell`) for document content,
  and by the kvstore coherent demo for time-travel snapshots.
- Apps store mutable state in the **16 fixed `SetField` slots**, not per-cell heaps
  (e.g. `starbridge-apps/subscription`'s queue is 8 slots). The heap — arbitrary
  committed `(collection,key)→value` memory — is a document/infrastructure feature,
  not yet an app-state pattern. **Mostly UNUSED at the app layer.**

### 3. Temporal caveats (rate / until / since / cooled / challenge)

Height-window `TemporalGate` is **deployed**; the register-reading atoms
(`RateBound`/`UntilEvent`/`SinceEvent`/`CooledSince`/`ChallengeWindow`) are
**proven** (`metatheory/Dregg2/Authority/TemporalAlgebra.lean:111-145`) and **wired**
to executor+circuit (`turn/src/executor/mod.rs:253+`, tags 13-16) but **staged**.

- **USED**: only `starbridge-apps/polis/src/lib.rs:705` (amendment cooling via the
  height-only `TemporalGate`; tested `starbridge-apps/polis/tests/deos_seam.rs:114-160`).
- The powerful register-read atoms (rate-limited caps, "valid-until" subscriptions,
  challenge windows) have **no app user and no app-writable SDK surface**.
  `subscription` rate-limits with a `MonotonicSequence` slot, not `RateBound`.

### 4. Conditional / eventual / promises (CapTP pipelining)

`turn/src/conditional.rs` (`ConditionalTurn`/`ProofCondition`), `turn/src/eventual.rs`
(`EventualRef`/`Pipeline`/`PipelineBuilder`), `turn/src/pending.rs` (promise-holes /
broken-promise propagation), `captp/src/pipeline.rs` (promise pipelining).

- **UNUSED** — zero app or demo exercises conditional batches, eventual references,
  promise pipelining, or guarded holes. The broadest gap in the tree.

### 5. Membrane fork/stitch + branch-and-stitch multiplayer

`docs/deos/BRANCH-AND-STITCH-PROTOCOL.md`, `SettlementSoundness.lean` (PROVEN), the
production `stitch_pair`/`ForkMembraneHost` in `starbridge-v2/src/{world,shared_fork}.rs`.

- **UNUSED at the app layer.** The production multiplayer fork/stitch is wired and
  tested only inside starbridge-v2 (`starbridge-v2/tests/stitch_pair_settlement_sound_production.rs`).
  `starbridge-apps/kvstore/tests/coherent_stack_demo.rs` forks/stitches at the
  *document* layer (`dregg_doc::merge`), not the distributed-world layer.

### 6. Time-travel / RCCS reversibility

`turn/src/reversible.rs` (`ReversibleHistory`/`Inversion`), `turn/src/umem.rs`
(`project_ledger`/`reify_ledger`), `docs/deos/FIRST-CLASS-REVERSIBILITY.md`.

- **PARTIAL**: `kvstore/tests/coherent_stack_demo.rs:284-311` uses
  `project_ledger`/`reify_ledger` to snapshot+restore a whole-ledger boundary at a
  past height (byte-identical). The full `ReversibleHistory` / per-effect `invert`
  (clean/contextual/committed un-turns) is **unused** by any app.

### 7. Mint / Burn supply model

`Effect::Mint`/`Effect::Burn` (`turn/src/action.rs:1407,1283`), `apply_mint`/`apply_burn`
(`turn/src/executor/apply.rs:2765,2547`).

- **UNUSED in production** — only `starbridge-apps/escrow-market/tests/cross_app_value_flow.rs:125`
  mints (in a test). Apps are value-agnostic (scalar fields), never minting their own
  asset wells.

### 8. Attenuation/delegation · light-client/attested queries · ring/intents/promises

- **Cap attenuation/delegation** (`cell/src/{capability,delegation}.rs`,
  `Effect::{AttenuateCapability,RevokeDelegation,RefreshDelegation}`): **1 app** —
  `starbridge-apps/tool-access-delegation/src/service.rs:40` (revoke + narrowed grant).
  Faceting / `AttenuateCapability` direct-use: unused.
- **Whole-history light-client / attested queries** (`dregg-query`): **2 apps,
  audit-only** — `agent-provenance/src/derived.rs`, `supply-chain-provenance/src/derived.rs`
  (`attested_*_log` over the receipt MMR). Never used for live mutable-state assertions.
- **Ring / intents / partial-turns / promises** (`intent/`, `app-framework/src/ring_trade.rs`,
  `Effect::{Promise,Notify,React,PipelinedSend}`): the coordinator was just wired
  (`RingTradeParticipant`→`RingSolver`) but **no starbridge-app implements a participant**
  and no app uses Promise/Notify/React. Adoption vacuum.

---

## Ranked by inspiring Houyhnhnm-demo value

The ranking weights *how many Houyhnhnm properties a real app would visibly
demonstrate* against *tractability of a clean, disjoint demo this lane can build*.

| # | Pillar → demo | Houyhnhnm properties shown | Tractability |
|---|---|---|---|
| **1** | **SealedEscrow atomic fair-exchange** — a real app trades value "I give X iff you give Y" through the proven capacity | capability-secure · witnessed · atomic/persistent (+ the canonical ocap *escrow exchange agent*) | **HIGH** (pure `cell` API, disjoint from escrow-market) — **LANDED** |
| **2** | **Branch-and-stitch multiplayer** — two agents fork the world, diverge, stitch under settlement-soundness | distributed · reversible · witnessed · **branch-and-stitch** · persistent | MEDIUM (production `stitch_pair` lives in starbridge-v2) |
| **3** | **Promise-pipelined coordination** — apps coordinate via `EventualRef`/`Pipeline`/CapTP without round-trips | distributed · capability-secure · witnessed (the E/Houyhnhnm lineage itself) | MEDIUM (turn-level API, no app precedent) |
| **4** | **Time-travel / undo on a live app** — `ReversibleHistory` un-turns an app's history to a past consistent state, stopping at committed boundaries | reversible · witnessed · persistent | HIGH (extends the kvstore `project_ledger` slice) |
| **5** | **Hatchery minting user-defined service kinds** + Mint/Burn — an app mints its own asset well and spawns child service-cells | persistent · content-addressed · capability-secure (generative) | MEDIUM |

### The chosen flagship — LANDED: a real SealedEscrow atomic swap

**Landed.** `demo/tests/sealed_escrow_atomic_swap.rs` now drives the proven
`dregg_cell::escrow_sealed` capacity end to end, and `escrow-market` itself was
regrounded onto the capacity (`SealedEscrowMarket`) — so the census's most glaring
fake (`escrow-market` hand-rolling escrow from slot caveats while the proven
`SealedEscrow` capacity sat unused) is now demolished on both fronts. The rest of
this section is the design rationale that drove that build.

**Why.** It was the single most *tractable* "real app drives a proven capacity end to
end" demo. The escrow-exchange agent is also the *canonical object-capability /
agoric-commerce pattern* (Miller's E / Agoric "escrow exchange") — the bedrock of
trustless distributed agent commerce, which is exactly the Houyhnhnm picture of
mutually-suspicious agents exchanging value safely.

**What it shows.** Two mutually-distrustful parties exchange value across two asset
wells with **no trusted intermediary**: each locks one leg into a witnessed escrow
cell (the leg is bound into the cell's canonical commitment — a light client *sees*
value enter); settlement completes **atomically** only when both conforming legs are
present, moving each leg to its counterparty; **value is conserved** across the whole
system; and the **half-open-trade attack** (counterparty never reciprocates) is
defeated by reclaim — no party can ever walk away holding the other's leg without
having genuinely deposited its own.

**Where it lives.** `demo/tests/sealed_escrow_atomic_swap.rs` — a new, disjoint
integration test that plays the executor role honestly (the escrow module decides
*when and how much* value may move via `settle()`'s authorized `(amount_a, amount_b)`;
the demo performs the wallet moves and asserts conservation), driving the REAL
`dregg_cell::escrow_sealed` API. It does **not** touch `escrow-market`.

**The honest scope of this slice.** The demo exercises the capacity at the
`cell` + balance-ledger layer (the layer the proven API operates at), as a multi-cell
value-flow narrative with conservation — strictly richer than the existing per-cell
unit tests in `escrow_sealed.rs`, which test the gate in isolation without value
flow. The named next slice (already flagged in `escrow_sealed.rs:77-85`) is the
in-circuit `SettleEscrow` effect so a *light client* — not just a re-executing
validator — witnesses settlement atomicity; that is a VK-affecting weld, out of
scope for this demo lane.

---

## The single most inspiring next thing to build

After this flagship lands, **branch-and-stitch multiplayer as a real app** (#2) is
the highest-leverage build: it is THE distributed-Houyhnhnm synthesis
([[DISTRIBUTED-HOUYHNHNM-FRONTIER]]) with the `SettlementSoundness` theorem already
proven, and the only thing missing is an *app* (not a starbridge-v2 internal test)
that forks a shared world between two agents, diverges them, and stitches under the
settlement-sound gate — turning a proven theorem into a playable multiplayer story.
The tractability cost is factoring `stitch_pair` out of starbridge-v2 into a
reusable turn/cell-level primitive a plain demo can call.

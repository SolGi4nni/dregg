# DreggDL for app deployment — deploy a starbridge-app, and the gate catches the over-grant

DreggDL ([`dregg-deploy/`](../dregg-deploy)) is dregg's declarative deployment
layer: a deployment is written once as a capability LAYOUT (TOML/JSON), lowered
to the exact `dregg_turn::CallForest` the SDKs instantiate, and CHECKED — whole —
before any gas. This document teaches what DreggDL does for **deploying a real
starbridge-app**: describing an app's factory births + capability grants as one
spec, and having the no-amplification + behavioral-refinement gates catch an
over-grant *before* anything ships.

For the algebra behind the behavioral gate see
[`DREGGDL-REFINEMENT.md`](./DREGGDL-REFINEMENT.md); for the polyglot lowering see
[`CAPDL-POLYGLOT-DX.md`](./CAPDL-POLYGLOT-DX.md). This doc is the app-deployment
face.

## 1. A deployment is the app's authority layout, written once

A starbridge-app is a factory (whose `state_constraints` ARE the app's policy,
installed on every born cell) plus the agent cells that hold capabilities over
the app cells. A DreggDL spec describes exactly that deployment:

| DreggDL section | what it is | lowers to |
|---|---|---|
| `[[factory]]` | the app's constructor-contract, by `ref` | a `FactoryDescriptor` (its on-chain VK is `factory_vk`) |
| `[[cell]]` | a cell born from a factory, by `name` | `Effect::CreateCellFromFactory` |
| `[[fund]]` | a funding transfer `from → to` | `Effect::Transfer` (conservation B is checked) |
| `[[grant]]` | one capability edge `from → to` over `target` | `Effect::GrantCapability` |

Reading the `[[grant]]` rows off the file **is** reading the whole capability
graph of the deployment — the CapDL property, made checkable.

**Pinning the real factory.** Set a `[[factory]]`'s `factory_vk` to a published
app factory VK (e.g. `starbridge-escrow-market`'s `ESCROW_FACTORY_VK`) and the
born cell's `CreateCellFromFactory` effect names *that* factory — so the deploy
instantiates the **real** on-chain factory, not a self-contained stand-in. Absent
a pin, the lowering derives a self-contained VK from the descriptor (a deployment
that stands alone without a published circuit).

The crate ships runnable specs for three deos-native apps under
[`dregg-deploy/specs/`](../dregg-deploy/specs): `supply-chain-provenance`,
`escrow-market`, `identity` — each pins its app's published factory VK and
describes the app's agent ladder + grant graph.

## 2. Capabilities are named by FACET, not by hex mask

A grant's authority over its target is restricted by an **effect facet** — which
effect KINDS the capability permits (the E-language restricted-object-view). The
raw form is a `u32` bitmask; DreggDL's surface is the readable
`dregg_cell::facet` vocabulary:

```toml
[[grant]]
from   = "manufacturer"
to     = "custodian"
target = "item"
facet  = "state_writer | transfer"   # write the custody slots + move the item
```

`facet` accepts a **named facet** (`read-only` · `transfer-only` · `state-writer`
· `admin` · `delegator` · `all`), a `|`/`+`/`,`-joined **list of effect kinds**
(`transfer | emit_event`, `set_field + grant_capability`, …), or a raw
decimal/hex mask. A named facet and a Rust-SDK `FACET_*` denote the same
authority. The low-level `allowed_effects = <u32>` still works (round-trip
stability); setting both is allowed only when they AGREE.

This is what lets a diagnostic name an over-grant in *words* (`state-writer
{SetField, EmitEvent}` vs `read-only {EmitEvent}`) instead of `Some(17)` vs
`Some(16)`.

## 3. The gates: ACCEPT a correct deploy, REFUSE an over-grant — named

A DreggDL deployment passes through two independent gates.

### (a) the static safety gate — no-amplification + conservation

`dregg-deploy check` / `dregg-deploy apply` runs
`dregg-userspace-verify::analyze` over the **whole** lowered forest:
conservation B (funding transfers net to zero), non-amplification A (every grant
edge is an attenuation of a cap the chain handed the grantor), structural
well-formedness. `apply` is the GATE: it refuses to emit a single turn for a
failing spec — **an over-grant is caught as an in-forest capability
amplification before any gas**.

The refusal is NAMED. When `verifier` (holding a read-only cap over `item`)
re-delegates a wider state-writer cap, the gate reports:

```
OVER-GRANT at node 5.0.0 effect[0]: `verifier` → `rogue-custodian` grants a
capability over `item` (slot 0, facet state-writer {SetField, EmitEvent}, expiry
never) — but `verifier` was only handed facet read-only {EmitEvent} for `item`
earlier in this deployment. The re-delegation WIDENS authority it does not hold
(it must be ⊆ the parent cap). Narrow `rogue-custodian`'s facet to within
read-only {EmitEvent}, or grant `verifier` the wider cap first.
```

It names the **edge** (`from → to`, by spec name), the **target**, the **granted
facet** and the **held parent facet** (in words), and suggests the fix. The
enrichment lives in [`dregg-deploy/src/diagnose.rs`](../dregg-deploy/src/diagnose.rs):
it re-walks the lowered forest at the finding's locus, recovers the actual
`GrantCapability` effect and the parent cap it failed to attenuate, and renders
them spec-named — purely additive over the underlying located `Finding`.

### (b) the behavioral refinement gate — FlowRefine

The lowered turn-sequence is a **flow**; `refines_upgrade(new, old)` decides
`new ≤ᶠ old` (the sound+complete FlowRefine simulation game). A redeploy that
WIDENS the running deployment — adds a reachable effect or a wider cap the
running one never had — is rejected, and the finding names the **diverging
effect** (`describe_diverging_effect`): not an opaque letter but the concrete
effect (`GrantCapability deal → bank over deal (facet unrestricted …)`), so the
operator sees *what* widened. A correct deploy `refines ✓` its declared envelope
(`refines_intent`). See [`DREGGDL-REFINEMENT.md`](./DREGGDL-REFINEMENT.md).

The two gates are different properties (a spec can pass static safety yet widen a
running deploy, and vice versa). The static gate runs unconditionally in `apply`;
the refinement gate is consulted by a redeploy pipeline with a running target.

### the demonstration

[`dregg-deploy/examples/app_deploy.rs`](../dregg-deploy/examples/app_deploy.rs)
runs both gates over all three apps' accept + over-grant specs:

```
cargo run -p dregg-deploy --example app_deploy
```

For each app it prints: the correct spec ACCEPTED (no-amp ✓, conserves ✓,
refines ✓, the per-root turn sequence + a linked receipt chain), and the
over-granting sibling REFUSED before any turn with the offending edge named, and
the same widening independently caught by FlowRefine. It exits 0 iff every accept
is accepted and every over-grant refused — a self-contained smoke test of the
story.

## 4. The planned receipt is an honest SHAPE, not a forged live receipt

`apply` emits, per turn, a `ProjectedReceipt`
([`dregg-deploy/src/apply.rs`](../dregg-deploy/src/apply.rs)) split HONESTLY into
two halves:

- the **artifact-known** half — computable off the turn alone at plan time (turn
  hash, forest hash, effects hash, agent, federation, action count, the
  `chain_link_hash` the next turn points at) — as plain values;
- the **executor-filled** half — the pre/post-state commitments, the computrons
  charged, the timestamp, the executor signature — typed
  `DeferredField::Deferred` until the live submit fills them.

These dynamic fields are **not zeroed-and-pretended**: a reader cannot mistake a
planned receipt for a live one with an all-zero post-state. The chain link is
still a pure function of the artifact (the unknown fields enter the *digest* as
their zero placeholders, as a chain SHAPE must), so the plan is a self-consistent
receipt chain at plan time; `AppliedPlan::chain_is_linked()` and
`receipts_are_planned_shape()` witness both facts. When the turns are submitted,
the SDK swaps each `Deferred` to `Filled(..)` from the executor's response — the
plan becomes a live receipt chain in place, checkable link-for-link against this
shape.

This is the disposition of the maturation-ledger Theme-3 finding (`apply.rs`
"the deploy receipt is a zeroed shape"): the receipt no longer reads as a live
receipt; the deferred half is **typed as deferred**. (Wiring the fields to a live
executor response at submit is the remaining step — it is now a typed swap, not a
silent overwrite of a zero.)

## Where it lives

- [`dregg-deploy/specs/`](../dregg-deploy/specs) — the app-deploy specs (accept +
  over-grant) for `supply-chain-provenance`, `escrow-market`, `identity`.
- [`dregg-deploy/examples/app_deploy.rs`](../dregg-deploy/examples/app_deploy.rs)
  — the runnable accept/reject demonstration over all three apps.
- [`dregg-deploy/src/facet.rs`](../dregg-deploy/src/facet.rs) — the named-facet
  parser + the human facet describer.
- [`dregg-deploy/src/diagnose.rs`](../dregg-deploy/src/diagnose.rs) — the enriched
  spec-named, facet-described diagnostics over a lowered assurance.
- [`dregg-deploy/src/apply.rs`](../dregg-deploy/src/apply.rs) — the gate
  (`plan_apply`), the per-root turn sequence, and the honest `ProjectedReceipt`
  shape (`DeferredField`).
- [`dregg-deploy/src/lower.rs`](../dregg-deploy/src/lower.rs) — name resolution,
  the facet/`factory_vk` lowering, and the delegation forest the no-amplification
  check walks.

## Honest seams

- **The receipt's dynamic half is deferred, not yet live.** `ProjectedReceipt`'s
  executor-filled fields are typed `Deferred`; populating them requires a live
  executor response at submit (there is no executor at plan time). The type now
  makes the boundary explicit; the live wiring is a typed swap to be done by the
  submit path.
- **The refinement gate is a Rust mirror of `FlowRefine.decideRefines`**, not yet
  a Lean-FFI call — see [`DREGGDL-REFINEMENT.md`](./DREGGDL-REFINEMENT.md) §6.
- **The static check is artifact-only.** A `Pass` certifies the declared layout
  conserves + does not amplify *within the forest*; it does NOT replace the
  executor (holding, balances, credentials, freshness, the state commitment are
  all live checks). DreggDL is a convenience + an audit artifact, never a trust
  boundary: a malformed DreggDL produces turns the executor rejects; it cannot
  produce an unsafe deployment the executor would accept.

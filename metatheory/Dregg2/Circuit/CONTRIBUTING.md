# Contributing to dregg2 circuits (a guide for Composer & other agents)

This is a **living, accurate** guide (last verified against the build at commit pending Gate 2/3 —
`lake build Dregg2` green at **3664 jobs**). Lean 4.30 / mathlib v4.30. If you change
the code and a claim here goes stale, **fix this file too**. Trust the *code* over any prose; if in
doubt, `lake build` it.

## 0. What this is

`dregg2` is a formally-verified web3 capability-OS written in **Lean 4** (`metatheory/`, an l4v-shaped
proof project; the git root is `/Users/ember/dev/breadstuffs`). The current crown jewel is the
**circuit ⟺ protocol** correspondence: we *derive ZK circuits in Lean* and prove they are a sound +
complete refinement of the protocol's real executor — so an Orchard-class value-forgery is impossible
**by construction**, and the verified circuit can drive a real Plonky3 prover.

## 1. The non-negotiable discipline (read first)

- **The green build IS the gate.** Every theorem you "prove" must `lake build` green. A green build with
  passing `#assert_axioms` is the *only* acceptance. Self-reports ("it builds") are not trusted — the
  reviewer re-builds.
- `export PATH="$HOME/.elan/bin:$PATH"` before any `lake`/`lean`.
- **Build command:** `lake build Dregg2.Circuit.<Module>` (one module) or `lake build Dregg2` (root).
- **NEVER** run `cargo test --lib` or `cargo test` without an exact test name in `circuit/` — the Rust
  lib suite takes **30+ minutes**. Use `cargo build -p dregg-circuit` + `cargo test -p dregg-circuit
  <exact::path> -- --exact`.
- **NO** `sorry` / `admit` / `native_decide` / new `axiom`. Pin every keystone with `#assert_axioms
  <name>` — it must whitelist exactly `{propext, Classical.choice, Quot.sound}`. A leaked `sorryAx`
  fails the build (that's the tripwire working).
- **Never** make `/tmp` "backup" copies and restore from them — that loses work. Edit in place; WIP
  files are git-untracked and the human/main-loop commits.
- **Additive, not destructive.** Do not rewrite the proven keystones (`StateCommit`, `SetFieldCommit`,
  `EffectCommit`, `EffectCommit2`, `Transfer`). Add new files under `Inst/`; if you must touch a shared
  file, keep its theorems intact and re-gate it.

## 2. The architecture — the circuit⟺spec triangle, per effect

For each protocol effect E there is a **three-corner triangle** (this is the anti-"pale-ghost" design):

```
                eSpec  (an INDEPENDENT declarative full-state post-state — the apex truth)
               /                                          \
   executor ⟺ eSpec                                    circuit ⟺ eSpec
   (the real executor produces exactly eSpec)          (a satisfying witness pins exactly eSpec)
```

- **eSpec** is full-state: it pins **every** field of the post-state. `RecordKernelState` has **17**
  fields (`accounts, cell, caps, escrows, nullifiers, revoked, commitments, bal, queues, swiss,
  slotCaveats, factories, lifecycle, deathCert, delegate, delegations, sealedBoxes`); `RecChainedState`
  adds the receipt `log`. **Miss one field in the frame and the spec is itself a ghost.**
- **executor ⟺ spec** lives in `Dregg2/Circuit/Spec/<family>.lean` (31/31 effect families done — see
  `<exec>_iff_spec` lemmas). This validates the executor against the independent spec.
- **circuit ⟺ spec** is the ZK part. As of the current build, **all 31 executor⟺spec families** have at
  least one full-state `*_full_sound` instance (see §7). Dispatch-aliased variants (e.g.
  `createObligationA` = `createEscrowA`, `fulfillObligationA` = `refundEscrowA`) inherit the same
  circuit. Composite meta-actions (`exerciseA`, `queueAtomicTxA`) remain out of scope (§8).

## 3. Which framework? (the decision tree)

The 17 kernel fields reduce to **three commitment shapes**. Pick the framework that matches the touched
component(s):

| Touched component | Framework | Carrier | Template |
|-------------------|-----------|---------|----------|
| `cell` map (1+ cells) | **v1 `EffectCommit`** | `frameDigest` / `FrameDigestBindsCells` | `Inst/incrementNonceA.lean` (propBit guard) or `EffectInstances.lean` (`setFieldE`, multi-bit guard) |
| `bal` / `caps` (whole function) | **v2 `EffectCommit2`** | `funcComponent` + injective whole-function digest | `Inst/mintA.lean` (bal) or `Inst/attenuateA.lean` (caps) |
| `List` side-table | **v2 `EffectCommit2`** | `listComponent` + `ListDigestBindsList` | `Inst/noteCreateA.lean` or `Inst/queueAllocateA.lean` |
| Log only (kernel frozen) | **v1 `EffectCommit`** with `touched := ∅` | log hash only | `Inst/emitEventA.lean` |
| 2 components (`bal` + `escrows`, `accounts` + `bal`) | **v2-dual `EffectCommit2Dual`** | two `ActiveComponent`s + two bind gates | `Inst/createEscrowA.lean`, `Inst/createCellA.lean` |
| 3 components (`queues` + `bal` + `escrows`) | **v2-triple `EffectCommit3`** | three `ActiveComponent`s + three bind gates | `Inst/queueEnqueueA.lean` |
| 4 components (factory create) | **v2-quad `EffectCommit4`** | four bind gates | `Inst/createCellFromFactoryA.lean` |
| 5 components (`spawnA`) | **v2-quint `EffectCommit5`** | five bind gates | `Inst/spawnA.lean` |
| `accounts` growth | **`AccountsCommit.accountsComponent`** | sorted-`Finset` list digest | `Inst/createCellA.lean` |

**Critical:** v1's `kernelFrame` lists `bal` before `escrows`; most bespoke specs list `bal` after
`commitments`. The `apex_iff_*` bridge always needs an **And-reassoc** (copy `setFieldE` in
`EffectInstances.lean` or `incrementNonceA` in `Inst/`).

**Critical:** `bal` uses `funcComponent` (whole-function digest), NOT `keyedComponent` — the
`CellId × AssetId` domain is infinite; a finite-carrier keyed digest cannot bind it.

## 4. The per-effect recipe (v1 — cell-changing effects)

Adding circuit⟺spec for a cell effect is a **thin instance** (~100 lines) in `Inst/<effect>.lean`:

1. An `EffectSpec St Args` value: `view`, `touched` (`Finset CellId`), `expectedLeaf`, `logUpdate`,
   `guardGates`, `guardProp`, `guardWidth` (≤ 64), `guardEncode`, `guardLocal`, `guardWidth_le`.
2. `GuardDecodes` / `GuardEncodes` — usually `propBit = 1 ↔ guardProp` at wire `0` (guardWidth = 1).
3. `apex_iff_<BespokeSpec>` — `touchedCellMap` collapse + `kernelFrame` And-reassoc.
4. `<effect>_full_sound` — compose `effect_circuit_full_sound` with the apex bridge.

The generic theorems (`effect_circuit_full_sound`, `_complete`, four anti-ghost teeth, emission) are
proved **once** in `EffectCommit.lean`.

**Log-only variant:** set `touched := fun _ _ => ∅`, `expectedLeaf := fun s _ c => s.kernel.cell c`,
`logUpdate := some (…)`. The post-cell clause with `T = ∅` pins `kernel.cell` unchanged.

## 5. The per-effect recipe (v2 — single non-cell component)

Adding circuit⟺spec for a bal/list/caps effect is a **thin instance** (~80–100 lines) in
`Inst/<effect>.lean`:

1. A `RestIffNo<Field> RH` portal (1-line mirror of `RestIffNoBal` / `RestIffNoNullifiers` in
   `EffectCommit2.lean` — omit the touched field from the frame hash).
2. An `EffectSpec2 St Args` value: `view`, `active` (`funcComponent` or `listComponent`), `logUpdate`,
   `restFrame` (verbatim bespoke spec frame order), guard sub-system.
3. `GuardDecodes2` / `GuardEncodes2`, `RestFrameDecodes2`.
4. `apex_iff_<BespokeSpec>` — usually a direct identity (match frame field order to the spec).
5. `<effect>_full_sound` — compose `effect2_circuit_full_sound` with the apex bridge.

The generic v2 theorems are proved **once** in `EffectCommit2.lean`. Carriers:
`ListCommit.ListDigestBindsList`, `KeyedCommit.KeyedDigestBindsKeys` (for finite keyed domains only).

## 5b. The per-effect recipe (v2-dual — two non-cell components)

For `bal`+`escrows` (or any two-component effect), ~100 lines in `Inst/<effect>.lean`:

1. A `RestIffNo<Field1><Field2> RH` portal omitting BOTH touched fields from the rest hash.
2. An `EffectSpec2Dual` with `active1` + `active2` (`funcComponent` + `listComponent` typical).
3. `GuardDecodes2Dual` / `GuardEncodes2Dual`, `RestFrameDecodes2Dual`.
4. `apex_iff_<BespokeSpec>` bridge.
5. `<effect>_full_sound` via `effect2dual_circuit_full_sound`.

Template: `Inst/createEscrowA.lean`. Wire indices `64..73` (`traceWidth = 74`); tactic `ec2d_lookup`.

## 5c. The per-effect recipe (v2-triple / quad / quint)

For 3–5 touched non-`cell` components, mirror `EffectCommit3`/`EffectCommit4`/`EffectCommit5`:

1. A `RestIffNo*` portal omitting ALL touched fields from the rest hash.
2. An `EffectSpec2Triple` / `EffectSpec2Quad` / `EffectSpec2Quint` with `active1`..`activeN`.
3. Guard/rest-frame decode lemmas + `apex_iff_<BespokeSpec>`.
4. `<effect>_full_sound` via `effect2triple_circuit_full_sound` (or quad/quint).

Wire indices: triple `64..75` (`traceWidth = 76`, `ec2t_lookup`); quad `64..77` (`78`, `ec2q_lookup`);
quint `64..79` (`80`, `ec2u_lookup`).

## 6. Proof-strategy playbook (the reusable tactics — avoid the known tarpits)

- **Wire lookups: use CONCRETE indices.** The digest wires are fixed literals (`64..73`), so the
  `reduceIte` simproc collapses the encoder's `if`-cascade automatically. The reusable tactic is
  **`ec_lookup`** (= `simp [encodeE, <wire abbrevs>]`). **Do NOT** use symbolic offsets like
  `guardWidth + k` in `if`-conditions — that triggers the `omega`-inside-`if_neg` metavariable tarpit.
- **`omega` over `Var`:** `Var` is `abbrev Var := Nat`, but in some spots you must `unfold Var at *`
  before `omega` sees it as `Nat`. For contradiction branches prefer `exfalso; omega`.
- **`StateCommit.FrameDigestBindsCells`** takes `CH compressN` as the **first explicit args** (then
  `hN hL k k' S h`). Forgetting them gives an "application type mismatch".
- **v1 frame `funext`** (post cell map reconstruction) cases on `c ∈ T` (decidable Finset
  membership): touched → `expectedLeaf`, live-untouched → frozen, dead → `AccountsWF`.
- **v2 needs NO funext** — `ActiveComponent.binds` gives the post-shape directly from the digest EQ.
- When a closed-form proof fights a `simp` normalization, exhibit the meaning with decidable `#guard`s
  and move on; note the deferral honestly.

## 7. Coverage map (current build — update when you add instances)

### Circuit⟺spec DONE (in root `lake build Dregg2`)

| Effect | Spec | Framework | Module |
|--------|------|-----------|--------|
| Transfer (recKExec) | TransferSpec | bespoke | `StateCommit.lean` |
| setFieldA | SetFieldSpec | bespoke + v1 template | `SetFieldCommit.lean`, `EffectInstances.lean` |
| transferE (framework validation) | TransferSpec | v1 | `EffectInstances.lean` |
| incrementNonceA | IncrementNonceSpec | v1 | `Inst/incrementNonceA.lean` |
| setPermissionsA | SetPermissionsSpec | v1 | `Inst/setPermissionsA.lean` |
| setVKA | SetVKSpec | v1 | `Inst/setVKA.lean` |
| receiptArchiveA | ReceiptArchiveSpec | v1 | `Inst/receiptArchiveA.lean` |
| refusalA | RefusalSpec | v1 | `Inst/refusalA.lean` |
| makeSovereignA | MakeSovereignSpec | v1 | `Inst/makeSovereignA.lean` |
| emitEventA | EmitEventSpec | v1 (log-only) | `Inst/emitEventA.lean` |
| mintA | MintASpec | v2 bal | `Inst/mintA.lean` |
| burnA | BurnSpec | v2 bal | `Inst/burnA.lean` |
| bridgeMintA | InboundMintSpec | v2 bal | `Inst/bridgeMintA.lean` |
| balanceA / transfer (asset) | BalanceMovementSpec | v2 bal | `Inst/balanceA.lean`, `Inst/transfer.lean` |
| noteCreateA | NoteCreateASpec | v2 list | `Inst/noteCreateA.lean` |
| noteSpendA | NoteSpendSpec | v2 list | `Inst/noteSpendA.lean` |
| attenuateA | AttenuateSpec | v2 caps | `Inst/attenuateA.lean` |
| delegate / introduceA / validateHandoffA | DelegateSpec | v2 caps | `Inst/delegate.lean`, etc. |
| delegateAttenA | DelegateAttenSpec | v2 caps | `Inst/delegateAttenA.lean` |
| revoke / dropRefA / revokeDelegationA | RevokeSpec | v2 caps | `Inst/revoke.lean`, etc. |
| createSealPairA | CreateSealPairSpec | v2 list | `Inst/createSealPairA.lean` |
| sealA / unsealA | SealSpec / UnsealSpec | v2 list | `Inst/sealA.lean`, `Inst/unsealA.lean` |
| queueAllocateA / queueResizeA | QueueAllocateSpec / QueueResizeSpec | v2 list | `Inst/queueAllocateA.lean`, etc. |
| swissExportA | ExportSpec | v2 list | `Inst/swissExportA.lean` |
| createEscrowA | EscrowHoldingCreateSpec | v2-dual | `Inst/createEscrowA.lean` |
| releaseEscrowA | ReleaseEscrowSpec | v2-dual | `Inst/releaseEscrowA.lean` |
| refundEscrowA | RefundEscrowSpec | v2-dual | `Inst/refundEscrowA.lean` |
| bridgeLockA | BridgeOutboundLockSpec | v2-dual | `Inst/bridgeLockA.lean` |
| bridgeCancelA | BridgeOutboundCancelSpec | v2-dual | `Inst/bridgeCancelA.lean` |
| bridgeFinalizeA | BridgeFinalizeSpec | v2 escrows-only | `Inst/bridgeFinalizeA.lean` |
| createCommittedEscrowA | CommittedEscrowCreateSpec | v2-dual + §8 portal | `Inst/createCommittedEscrowA.lean` |
| createCellA | CreateCellSpec | v2-dual accounts+bal | `Inst/createCellA.lean` |
| createCellFromFactoryA | CreateFromFactorySpec | v2-quad | `Inst/createCellFromFactoryA.lean` |
| spawnA | SpawnSpec | v2-quint | `Inst/spawnA.lean` |
| queueEnqueueA | QueueEnqueueSpec | v2-triple | `Inst/queueEnqueueA.lean` |
| queueDequeueA | QueueDequeueSpec | v2-triple | `Inst/queueDequeueA.lean` |
| queuePipelineStepA | QueuePipelineFanoutSpec | v2 queues | `Inst/queuePipelineStepA.lean` |
| pipelinedSendA | PipelinedSendSpec | v1 log-only | `Inst/pipelinedSendA.lean` |

### Dispatch aliases (same circuit as the canonical variant)

| Alias | Inherits circuit from |
|-------|----------------------|
| `createObligationA` | `createEscrowA` |
| `fulfillObligationA` | `refundEscrowA` |
| `slashObligationA` | `releaseEscrowA` |
| `releaseCommittedEscrowA` / `refundCommittedEscrowA` | `releaseEscrowA` / `refundEscrowA` |

### Circuit⟺spec OUT OF SCOPE (composite meta-actions)

- **`exerciseA`** — dispatches an inner `List FullActionA` (composite, not a single effect family).
- **`queueAtomicTxA`** — batches multiple queue ops in one turn.

## 8. The cardinal sins (what makes a "proof" worthless)

- **Conservation ≠ full semantic correctness.** Pinning `Σδ = 0` over the moved cells + the entry guard
  is a *projection*, not soundness — an adversary can tamper with any unconstrained field. The whole
  post-state (all 17 fields + log) must be pinned. The anti-ghost teeth (`_rejects_third_cell`,
  `_rejects_field_tamper`, …) are the proof you did this.
- **Unrealizable portals.** Carry only **realizable** crypto assumptions (injectivity of genuine Poseidon
  hashes). A *sum* is not injective — `frameDigest` must be a real `compressN` sponge, never a
  `Finset.sum`.
- **The frame-portal ghost.** NEVER carry `postRoot = recStateCommit (applyEffect …)`. The frame must be
  *reconstructed* (by `funext` or `ActiveComponent.binds`), not asserted.
- **Field soundness needs range checks.** `ℤ`-soundness in Lean ≠ field-soundness after mapping to
  BabyBear (`p = 2³¹ − 2²⁷ + 1`). Range-check balances via lookups into `[0, 2^k)` with **`k ≤ 30`**.

## 9. The Rust side (the "swap")

`circuit/src/lean_descriptor_air.rs` is a generic Plonky3 AIR that interprets a Lean-emitted
`EmittedDescriptor` and drives the real `p3-uni-stark` prover. Lean is the verified source-of-truth;
Plonky3 is the prover.

**End-to-end proofs flowing (verified round-trips):**

| Lean circuit | Wire export (`#eval`) | Rust acceptance test |
|--------------|----------------------|----------------------|
| `Transfer.transferCircuit` (9 gates) | `transferDescriptorJson` | `lean_emitted_transfer_roundtrip` |
| `Transfer` + balance range checks | `transferDescriptorRangedJson` | `lean_emitted_transfer_field_sound` |
| `StateCommit.stateCircuit` (12 gates, full-state) | `stateDescriptorJson` | `lean_emitted_state_roundtrip` |
| `StateCommit` + balance range checks | `stateDescriptorRangedJson` | `lean_emitted_state_field_sound` |
| `SetFieldCommit.setFieldCircuit` (8 gates) | `setFieldDescriptorJson` | `lean_emitted_setfield_roundtrip` |
| `EffectInstances2.mintE` v2 effect (4 gates) | `mintDescriptorJson` | `lean_emitted_mint_roundtrip` |

Run: `cargo test -p dregg-circuit --lib lean_emitted --features plonky3` (fast; ~6 tests).

**Refinement tower** (`Refinement.lean`): `circuit ⊑ spec ⊑ exec` as explicit `Refines`/`Equiv` step-relations;
`emitted_equiv_arith` links the Plonky3 wire to `satisfied stateCircuit`; `stateCircuitL` + `circuitL_refines_spec`
add the lookup/range-check layer on top.

**v2 effect diamond** (`EffectRefinement.lean`): generic `effect2CircuitStep ⟺ apex` + `emitted ⟺ circuit` for
ANY `EffectSpec2`; concrete instances (mint, burn, …) compose with `exec*_iff_spec` for
`emitted ⟺ circuit ⟺ spec ⟺ execFullA`. Mint payoff: `mint_supply_delta_descends` (supply conservation
descends from the spec through refinement).

**Four balance wires ≠ booleans.** On `Transfer`/`StateCommit` they are the four **integer** balance
columns (`vSrcPre`/`vDstPre`/`vSrcPost`/`vDstPost`); `stateRanges` range-checks them into `[0, 2³⁰)` for
field soundness. The full-state circuit also carries **digest-binding EQ gates** (frame sponge, touched
cells, log hash) — not a standalone conservation flag. v2 effects (`mintE`, …) use the same digest
pattern at wires `66..71` (rest / component / log equality); the guard is one `propBit`, but soundness
pins the **whole** post-state via `effect2_circuit_full_sound`.

**Still open on the swap:** generic `EffectCommit` instances (v1/v2/…) auto-emit via `emittedEffect*`
but do not yet have per-effect Rust goldens; PART II/III wire forms (`MerkleHash`, `Polynomial`, …)
need decoder extensions for Poseidon2-in-circuit; gadget envelopes in `CircuitEmitGadgets` need Rust
AIR wiring.

## 10. Map of the key files

- `Dregg2/Circuit.lean` — the IR (`Expr` var/const/add/mul, `Constraint`, `satisfied`).
- `Dregg2/Circuit/Lookup.lean` — the lookup/range-check IR.
- `Dregg2/Circuit/Transfer.lean` — transfer bit-gate `*_iff` lemmas, `TransferSpec`.
- `Dregg2/Circuit/StateCommit.lean` — transfer bespoke full-state + CR carriers (`frameDigest`,
  `FrameDigestBindsCells`, injectivity portals, `AccountsWF`).
- `Dregg2/Circuit/SetFieldCommit.lean` — setFieldA bespoke full-state (+ growing log).
- `Dregg2/Circuit/EffectCommit.lean` — **v1 GENERIC** framework (cell + log-only effects).
- `Dregg2/Circuit/ListCommit.lean` — v2 list carrier (`ListDigestBindsList`).
- `Dregg2/Circuit/KeyedCommit.lean` — v2 keyed carrier (finite domains only).
- `Dregg2/Circuit/EffectCommit2.lean` — **v2 GENERIC** framework (single non-cell component).
- `Dregg2/Circuit/EffectCommit2Dual.lean` — **v2-dual GENERIC** framework (two non-cell components).
- `Dregg2/Circuit/AccountsCommit.lean` — accounts-growth carrier (`accountsComponent`).
- `Dregg2/Circuit/EffectCommit3.lean` — **v2-triple GENERIC** framework (three non-cell components).
- `Dregg2/Circuit/EffectCommit4.lean` — **v2-quad GENERIC** framework (four non-cell components).
- `Dregg2/Circuit/EffectCommit5.lean` — **v2-quint GENERIC** framework (five non-cell components).
- `Dregg2/Circuit/EffectInstances.lean` — v1 validation templates (`transferE`, `setFieldE`).
- `Dregg2/Circuit/EffectInstances2.lean` — v2 validation templates (`mintE`, `noteSpendE`).
- `Dregg2/Circuit/Inst/<effect>.lean` — **production instances** (one file per effect; this is what you add).
- `Dregg2/Circuit/Refinement.lean` — the l4v refinement tower.
- `Dregg2/Circuit/Spec/*.lean` — the 31 executor⟺spec families (bridge your `apex_iff_*` to these).
- After adding a module, wire its `import` into `metatheory/Dregg2.lean` and full-build `lake build Dregg2`.
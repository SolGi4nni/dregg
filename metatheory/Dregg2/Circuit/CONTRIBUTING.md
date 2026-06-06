# Contributing to dregg2 circuits (a guide for Composer & other agents)

This is a **living, accurate** guide (last verified against the build at commit pending — run
`lake build Dregg2` and update this line when you land work). Lean 4.30 / mathlib v4.30. If you change
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
- **circuit ⟺ spec** is the ZK part. As of the current build, **~32 effect variants** have full-state
  `*_full_sound` theorems (see §7 coverage table). The rest are deferred multi-component or
  accounts-growth effects (§8).

## 3. Which framework? (the decision tree)

The 17 kernel fields reduce to **three commitment shapes**. Pick the framework that matches the touched
component(s):

| Touched component | Framework | Carrier | Template |
|-------------------|-----------|---------|----------|
| `cell` map (1+ cells) | **v1 `EffectCommit`** | `frameDigest` / `FrameDigestBindsCells` | `Inst/incrementNonceA.lean` (propBit guard) or `EffectInstances.lean` (`setFieldE`, multi-bit guard) |
| `bal` / `caps` (whole function) | **v2 `EffectCommit2`** | `funcComponent` + injective whole-function digest | `Inst/mintA.lean` (bal) or `Inst/attenuateA.lean` (caps) |
| `List` side-table | **v2 `EffectCommit2`** | `listComponent` + `ListDigestBindsList` | `Inst/noteCreateA.lean` or `Inst/queueAllocateA.lean` |
| Log only (kernel frozen) | **v1 `EffectCommit`** with `touched := ∅` | log hash only | `Inst/emitEventA.lean` |
| 2+ components (escrow, enqueue, …) | **DEFERRED** — multi-component v2 extension | — | — |
| `accounts` growth | **DEFERRED** — set-digest carrier | — | — |

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

### Circuit⟺spec DEFERRED (executor⟺spec done; circuit corner open)

These touch **2+ components** or **accounts growth** — need multi-component v2 or a set-digest carrier:

- **Accounts growth:** `createCellA`, `spawnA`, `createCellFromFactoryA`
- **Escrow:** `createEscrowA`, `releaseEscrowA`, `refundEscrowA`, `createCommittedEscrowA`
- **Bridge outbound:** `bridgeLockA`, `bridgeFinalizeA`, `bridgeCancelA`
- **Queue pipeline:** `queueEnqueueA`, `queueDequeueA` (queues + bal + escrows), `queuePipelineStepA`,
  pipelined send with deposit

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
Plonky3 is the prover. The Lean→JSON→Rust wire is live for `transferCircuit`; emitting full-state
circuits with Poseidon2 gates is the next step.

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
- `Dregg2/Circuit/EffectInstances.lean` — v1 validation templates (`transferE`, `setFieldE`).
- `Dregg2/Circuit/EffectInstances2.lean` — v2 validation templates (`mintE`, `noteSpendE`).
- `Dregg2/Circuit/Inst/<effect>.lean` — **production instances** (one file per effect; this is what you add).
- `Dregg2/Circuit/Refinement.lean` — the l4v refinement tower.
- `Dregg2/Circuit/Spec/*.lean` — the 31 executor⟺spec families (bridge your `apex_iff_*` to these).
- After adding a module, wire its `import` into `metatheory/Dregg2.lean` and full-build `lake build Dregg2`.
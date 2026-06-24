# DESIGN: The Effect-Handler Algebra (the swap-grade executor foundation)

**Status:** design ACCEPTED (orchestrator-reviewed 2026-06-04). Scaffold building in `Dregg2/Exec/Handler.lean`.
**Why:** codex's two reviews + the dregg4 comodel vision converge: the executor is *"one giant inductive
(`FullActionA`, 56 ctors) + proof matrix"* — every new effect needs ≥6 unrelated hand-syncs
(dispatch/delta/receipt/obligation/codec/coloring), and Lean's exhaustiveness fires only *within* one
match, never relating them. **Every fidelity hole both reviews found is a missed sync.** Fix = an algebra of
effect handlers where the obligations are *types*, not conventions, so a handler cannot be registered
without its gates. (A handler-of-an-algebraic-effect-theory = a comodel = the dregg4 turn.)

## The `EffectHandler` record (obligations are PROOF fields → literal ill-typed until discharged)

```
structure EffectHandler (Args : Type) where
  -- identity
  tag : EffectKind ; wireTag : String ; color : LinearityClass
  -- data (one per scattered global match)
  step      : RecordKernelState → Args → Option RecordKernelState   -- = execFullA arm
  delta     : Args → AssetId → Int                                   -- = ledgerDeltaAsset arm; PER-ASSET, never scalar
  auth      : RecordKernelState → Args → Bool                        -- (v2: Guard-valued, Spec/Guard.lean, ⊓ = Guard.all MEET)
  admission : RecordKernelState → Args → Bool                        -- lifecycle/live gate (the R1 hole)
  trace     : Args → Turn
  -- OBLIGATIONS (registering FORCES these):
  auth_gated      : ∀ s a s', step s a = some s' → auth s a = true
  admission_gated : ∀ s a s', step s a = some s' → admission s a = true
  conserves       : ∀ s a s', step s a = some s' → ∀ b, recTotalAssetWithEscrow s' b
                                                       = recTotalAssetWithEscrow s b + delta a b
```

## Composition (the coproduct) — deliberately NOT a freer monad

`PackedHandler := Σ Args, EffectHandler Args`; `Registry := List PackedHandler` IS the coproduct of the
per-effect arg-theories. `Effect := Σ (p : PackedHandler), p.Args` (tag+payload) **REPLACES the closed
`inductive FullActionA`**. Dispatch is a LOOKUP not a 56-arm match: `execEffect R s ⟨p,args⟩ := p.h.step s args`.
The homomorphism out of the coproduct is `List.foldlM` (Plotkin–Pretnar "run under a handler" = the unique
hom). **No freer-monad / effect-row encoding** — that invites the `Type`-vs-`Type 1` / `TypeCat`-coercion
pain that bit the Intent co-Yoneda collapse ([[memory]]); `List PackedHandler` + Σ-carrier + `foldlM` sidesteps it.

## Derivation (the proof-matrix-killer)

Every global object becomes a **fold over the registry**, ONE generic theorem per axis instead of one arm
per ctor: `execFullA`/`ledgerDeltaAsset`/`fullReceiptA`/`encodeActionW`/`parseActionW` are projections
through lookup. `turn_conserves` = ONE generic `foldlM` induction using each handler's `conserves` field at
each step ⇒ **`execFullA_ledger_per_asset` (TEF:3517, the 56-arm cases matrix) CEASES TO EXIST.**

## Hole prevention: convention → type

Today a missing gate is SILENT (5 arms are total-`some` skipping gates; `emitEvent`/`pipelinedSend` gates
live inline in the dispatch body where no obligation sees them; the lifecycle gate `acceptsEffects` is read
by ONLY 3 of 56 arms and no obligation requires the other 53). After: you cannot construct the record
without `conserves`/`auth_gated`/`admission_gated`; a new effect that forgets a gate **does not typecheck**.

## Migration slice (parallel module first, NOT a cutover)

`Dregg2/Exec/Handler.lean`, 3-element registry, prove the derivation lemmas before scaling:
1. **conservation** rep = `balanceA`/transfer (`recKExecAsset_conserves_per_asset` @RecordKernel:764) — and
   this slice ADDS the missing lifecycle admission to transfer (closes R1, proving the refactor *closes*
   holes, not relocates them).
2. **authority** rep = `createEscrowA` (richest single effect; `escrow_create_conserves_combined_per_asset`
   @1522 + real `authorizedB`).
3. **admission** rep = a state/emit effect with the live-cell gate (non-trivial `admission_gated`).
Then migrate all 56 effects (after codec #136 frees the executor files). `revoke`/`attenuate` etc. become
*total* handlers with a `selfLimiting` (monotone-decrease) obligation instead of a faked `conserves`.

## VERIFIED HOLE INVENTORY (re-checked vs the current code — do NOT re-chase the stale ones)

REAL (become handler obligations as effects migrate):
- **R1** (headline) lifecycle admission `acceptsEffects` (TEF:1617) read by only seal/unseal/destroy — ~50
  effects accept transfers/writes/mints into Sealed/Destroyed cells. → `admission` field, closed in the slice.
- **R2** (#27) escrow release/refund (`releaseEscrowKAsset`/`refundEscrowKAsset` RecordKernel:1495/1505) take
  only `id`, no actor/authority; chained wrapper logs but doesn't check actor → anyone settles. → `auth`.
- **R3** (#27) `createSealPairChainA` (TEF:1811) no pid-freshness; `findSealedBox` first-match → dup pid
  shadows. → id-freshness conjunct in `admission`.
- **R4** `exerciseA` facet-mask (cap allowed_effects) not executable (only §8); inner effects run with
  inner-actor authority. → `facetMask` field on the recursive handler.
- **R5** (ember dual-ledger) `setFieldA` can write a record `"balance"` field (`writeField` EffectsState:181),
  disjoint from conserved `k.bal`. → quarantine `"balance"` / forbid the field, or prove the relation.
- **R6** `receiptArchiveA` writes `lifecycleField` via bare `stateStep` (TEF:3468), bypassing the cellSeal
  state-machine — 2nd ungated lifecycle path. → route through the same `admission`.
- **R7** 5 always-`some` arms (revoke/dropRef/revokeDelegation/attenuate/noteCreate/pipelinedSend) — but
  SOUND-BY-DESIGN (self-limiting monotone-decrease / authority-free by design); model as total handlers with
  `selfLimiting`, not a hole.
- **R8** heavy aliasing (fulfill==refund, slash==release, committed==plain, introduce==validateHandoff==delegate
  executably); distinguishing gates deferred to §8. Registry makes aliases explicit.
- **R9** (suspected→addressed) per-asset RUN-level conservation lift (vector proved per-turn; run-level on
  scalar). → the generic `foldlM` derivation proves it once.
- **R10** the quadruple/quintuple manual-sync burden — the whole refactor premise. → registry derivation.
- **R11** (credential binding, #28-adjacent) `parseWTurn` parses envelope agent/nonce/fee/validUntil/prevHash
  (FFI:2913) but `mkGAuth`/`liftForestG` build the gate only from the per-node credential — envelope not
  transported / "what was signed" not bound. → carry the envelope into the gate.
- **R12** (#28) `bridgeFinalize` delta/color: `effectLinearity .bridgeFinalize = Conservative`
  (CatalogInstances:281) while `fullActionInvA`:5315 asserts a `-amount` disclosed outflow. → reclassify
  (Disclosed-outflow color) so `color` and `delta` agree.

STALE / REFUTED (do NOT re-open — verified against current code):
- **S1** "bridgeFinalize doesn't check `r.bridge`" — FALSE: RecordKernel:1728 checks
  `r.bridge=true ∧ r.asset=asset ∧ r.amount=amount` + `bridgeAuthOK` (TEF:2703). (Confirms the orchestrator's
  own catch.)
- **S2** "anyone can finalize/cancel a victim bridge lock by id" — closed by `bridgeAuthOK` creator-only
  (TEF:2703). (Relayer foreign-receipt path is deferred-by-DESIGN to META-FILL E, not a bug.)
- (codex review #1 P1-4 factory `vk:Nat` negative-aliases-0 — NOT yet re-verified here; check
  `findFactory vk.toNat` @TEF:1004 separately before fixing.)

## Risks
- No freer-monad (avoids universe pain). Hardest Lean obligation deferred: termination of the recursive
  `exerciseA` handler (well-founded recursion on sub-effect-list size; `actionSize` @CodecRoundtrip:3332 is
  the fuel precedent).
- Heterogeneous-`Args` proofs over `Σ Args, EffectHandler Args` are awkward; folding `conserves` across a
  registry of differently-typed handlers needs care (the scaffold proves this works before scaling).
- Migration touches `TurnExecutorFull`/`RecordKernel` — gated on the codec #136 repair landing (collision).

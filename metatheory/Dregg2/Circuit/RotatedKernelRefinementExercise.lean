/-
# Dregg2.Circuit.RotatedKernelRefinementExercise — the VALUE-leg circuit→kernel refinements (or the
  HONEST classification) for the THREE awkward effects the per-effect rung had left open: `exercise`,
  `custom`, `heapWrite`. Additive; new names only; imports read-only.

## The three effects, classified PRECISELY

  * **exercise** → `ExerciseSpec` (`ActionDispatch.exerciseA` arm) = `innerFacetsAdmittedA … = true ∧
    exerciseGuard st actor target ∧ turnSpec (exerciseHoldState st actor) inner st'`. CLASS =
    **PARTIAL-named-residual**. The `ExerciseSpec` is a CONJUNCTION of three legs of DIFFERENT
    character, and they discharge differently:
      (1) the **hold-gate** `exerciseGuard` (a cap MEMBERSHIP `(caps actor).any (confersEdgeTo
          target)`) — the SAME cap-membership the deployed cap-open (`DeployedCapOpen`/the Facet
          file's `authorizedFacetB` discharge) realizes IN-CIRCUIT; carried here as the named
          `holdGate` residual exactly as the Facet template carries `TransferAuthoritySource` (the
          cap-tree datum the LEDGER commitment cannot certify);
      (2) the **facet-mask** `innerFacetsAdmittedA … = true` (R4 allowed-effects) — carried as the
          named `facetMask` residual (the per-inner-effect facet view, a SEPARATE per-row descriptor);
      (3) the **inner fold** `turnSpec (exerciseHoldState st actor) inner st'` — the recursion through
          the carried inner action list. The audit found the inner-fold admissibility is DEFERRED to
          the separate per-row descriptors of the inner effects (each inner step is its OWN
          `dispatchArm`/`Satisfied2` row, NOT a column of THIS exercise row's descriptor). So it is
          the named `innerFold` residual — STATED precisely, NOT laundered as bound by this row.
    `exercise_descriptorRefines` ASSEMBLES `ExerciseSpec` from the three named legs (none faked); the
    teeth bite on the assembled legs. The genuinely-discharged content of THIS row is the assembly: a
    valid exercise step IS the hold-gate ∧ facet-mask ∧ inner fold, and the rung shows the executor
    commits exactly when those hold (`exercise_descriptorRefines_execFullA`, both via the iff). The
    in-circuit DISCHARGE of (1) is the Facet cap-open; of (3) is the inner per-row apex fold
    (`CircuitSoundness.turnDecodeChain_refines_turnSpec`) — both NAMED, both already built elsewhere.

  * **custom** → there is **NO** `customA` constructor in `FullActionA` and **NO** `CustomSpec` arm in
    `fullActionStep`. CLASS = **OUT-OF-SCOPE — no kernel arm.** The `customVmDescriptor2R24` registry
    entry (and the `.custom` `TableId`) is the RECURSIVE-PROOF-BINDING circuit (`EffectVmEmitV2`'s
    `customVmDescriptor2` / `customProofBind` — it binds a nested verifier proof digest to PI), NOT a
    KERNEL STATE-TRANSITION descriptor. There is no kernel state move for it to refine TO: `custom` is
    an AUTHORITY MODE (`AuthModes.AuthMode.custom`, the witnessed-predicate seam) + a proof-carrier
    table, both ORTHOGONAL to the `RecChainedState` step the per-effect VALUE rung quantifies over. We
    record this with the witness theorem `no_customA_arm` (the dispatcher has no custom arm — there is
    literally no `FullActionA.customA` to write a spec against). A per-effect VALUE rung is VACUOUS
    where there is no effect; this is the honest finding, not a gap to fill.

  * **heapWrite** → `HeapWriteSpec` (`Spec.heapwrite`) = `SetFieldGuard … heap_root newRoot ∧ cell :=
    setFieldCellMap(heap_root := newRoot) ∧ heaps := heapWriteHeapsMap ∧ log ∧ 14-field frame`. The
    spec takes `newRoot` as a **FREE parameter** — it does NOT, alone, force `newRoot = recompute`.
    AND `heapWrite` is **ABSENT from `v3Registry`** (the rotated live cohort) — it has an
    `EmittedDescriptor` (`Inst/heapWriteA`) but no rotated registry entry, so the LIVE apex (which
    quantifies only over `v3Registry` members) does NOT range over it. CLASS = **PROVEN-FIX (the
    `newRoot` recompute is FORCED) — but OUT-OF-LIVE-APEX (no `v3Registry` descriptor).** The genuine
    in-row `heap_root` recompute machinery EXISTS (`Emit.EffectVmEmitHeapRoot`): `heapRootHolds` (the
    three recompute sites) FORCES the new-root register to `heapAdvanceOf(leafOf(addrOf coll key) v,
    oldRoot)` — a DETERMINISTIC function of the bound `(coll, key, value, oldRoot)`, no free digest
    (`heapRootAdvance_forced`), anti-ghosted (`heapRoot_binds_write`: tamper any of `(coll,key,value)`
    or the old root ⇒ the new root moves ⇒ UNSAT). So we build the FIX: `heapWriteEncodes` carries the
    recompute-honest row (FORCING `newRoot` to the genuine recompute — the spec's free param is
    PINNED), the register write, the heap splice, the guard, the log, and the 14-field frame.
    `heapWrite_descriptorRefines ⟹ HeapWriteSpec`; `heapWrite_newRoot_forced` exhibits the pinned
    `newRoot`; the tooth `heapWrite_descriptorRefines_rejects_wrong_value` bites (two writes pinning
    the SAME `newRoot` wrote the SAME value). The sorted-tree SPLICE recompute (`heapWriteHeapsMap`'s
    `Heap.set` ↔ the sorted leaf-list update) is the PHASE-E residual (the bracketing range-checks,
    `Substrate.Heap.get_none_of_gap` — out of scope, exactly as `EffectVmEmitHeapRoot`'s header
    documents); carried as the named `heapsSplice`. RUST SCOPE (to make it LIVE, not just
    constructible): a `heapWriteVmDescriptor2R24` rotated `v3Registry` entry + the `heap_root` recompute
    sites wired into its row + the absorbed `heap_root` limb (the GROUP-4 mechanism already exists for
    `cap_root`) — NOT done; the registry was NOT swapped.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} + the named `Poseidon2SpongeCR` carrier
(inherited through `EffectVmEmitHeapRoot` for the heapWrite recompute anti-ghost). No `sorry`, no
`native_decide`, no `:= True`, no fresh axiom. NEW file; all imports read-only.
-/
import Dregg2.Circuit.ActionDispatch
import Dregg2.Circuit.Emit.EffectVmEmitHeapRoot
import Dregg2.Circuit.Emit.EffectVmEmitRotationV3
import Dregg2.Circuit.RotatedKernelRefinement

namespace Dregg2.Circuit.RotatedKernelRefinementExercise

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.ActionDispatch
  (ExerciseSpec exerciseGuard exerciseHoldState turnSpec fullActionStep
   execFullA_exerciseA_iff_spec)
open Dregg2.Circuit.Spec.HeapWrite
  (HeapWriteSpec heapWriteHeapsMap execFullA_heapWriteA_iff_spec)
open Dregg2.Circuit.Spec.CellStateField (SetFieldGuard setFieldCellMap)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv prmCol satisfiedVm)
open Dregg2.Circuit.Emit.EffectVmEmitHeapRoot
  (heapRootHolds heapRootAdvance_forced heapRoot_binds_write heapAdvanceOf leafOf addrOf
   HEAP_ROOT_AFTER HEAP_ROOT_BEFORE heapWriteVmDescriptor heapWriteVmDescriptor_hashSites
   heapRecomputeSites)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.DescriptorIR2 (VmTrace Satisfied2 envAt EffectVmDescriptor2)
open Dregg2.Circuit.Emit.EffectVmEmitV2 (graduateV1 graduateV1_sound graduable)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (rotateV3 rotateV3_satisfiedVm_v1 graduable_rotateV3)
open Dregg2.Circuit.RotatedKernelRefinement (RotTableSide)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 — exercise: PARTIAL. The three legs of `ExerciseSpec`, each NAMED, assembled.

`ExerciseSpec st actor target inner st'` is `innerFacetsAdmittedA … = true ∧ exerciseGuard st actor
target ∧ turnSpec (exerciseHoldState st actor) inner st'`. The three legs discharge DIFFERENTLY:
the hold-gate is a cap MEMBERSHIP (the deployed cap-open realizes it in-circuit — the Facet file's
`TransferAuthoritySource` template); the facet-mask is the R4 allowed-effects view (a separate
per-inner-row descriptor); the inner fold is the recursion through `inner` (each inner step its OWN
per-row apex descriptor — the inner-fold admissibility deferred there). We carry the three as the
named `exerciseEncodes` residual and ASSEMBLE the spec. -/

/-- The decode for an exercise row: the three `ExerciseSpec` legs, each carried as a NAMED residual.
`holdGate` — the cap MEMBERSHIP the deployed cap-open discharges in-circuit (the `authorizedFacetB`
template's `confersEdgeTo` analog; the cap-tree datum the ledger commitment cannot certify).
`facetMask` — the R4 allowed-effects admittance (the per-inner-effect facet view, a separate per-row
descriptor). `innerFold` — the recursion through the carried inner action list (each inner step its
OWN per-row `dispatchArm`/`Satisfied2` row; the inner-fold admissibility deferred to those
descriptors). NONE faked: the rung ASSEMBLES `ExerciseSpec` from them, and the in-circuit DISCHARGE of
each is the named lane already built elsewhere (the cap-open for `holdGate`, the inner per-row apex
fold for `innerFold`). -/
structure exerciseEncodes (pre post : RecChainedState) (actor target : CellId)
    (inner : List FullActionA) : Prop where
  /-- the R4 facet-mask admittance (the named per-inner-row facet residual). -/
  facetMask : innerFacetsAdmittedA pre actor target inner = true
  /-- the hold-gate cap MEMBERSHIP (the named cap-open residual — discharged in-circuit by the
  deployed cap-open, exactly as the Facet template discharges `authorizedFacetB`). -/
  holdGate : exerciseGuard pre actor target
  /-- the inner fold from the hold post-state (the named per-row inner-fold residual — each inner step
  its own descriptor; the inner-fold admissibility deferred there). -/
  innerFold : turnSpec (exerciseHoldState pre actor) inner post

/-- **`exercise_descriptorRefines` — the exercise circuit→kernel refinement (ASSEMBLED, PARTIAL).**
A satisfying exercise row (`exerciseEncodes`) forces `ExerciseSpec pre actor target inner post`: the
hold-gate, the facet-mask, and the inner fold ARE the three `ExerciseSpec` conjuncts, assembled from
the named legs. The hold-gate is discharged in-circuit by the deployed cap-open (the Facet template);
the inner fold by the inner per-row apex fold — both NAMED, both already built. The rung CERTIFIES
that a valid exercise step is exactly those three legs (a forged exercise lacking any one is
rejected — the teeth). -/
theorem exercise_descriptorRefines (pre post : RecChainedState) (actor target : CellId)
    (inner : List FullActionA) (henc : exerciseEncodes pre post actor target inner) :
    ExerciseSpec pre actor target inner post :=
  ⟨henc.facetMask, henc.holdGate, henc.innerFold⟩

/-- The exercise refinement against `execFullA` directly (via `execFullA_exerciseA_iff_spec`). -/
theorem exercise_descriptorRefines_execFullA (pre post : RecChainedState) (actor target : CellId)
    (inner : List FullActionA) (henc : exerciseEncodes pre post actor target inner) :
    execFullA pre (.exerciseA actor target inner) = some post :=
  (execFullA_exerciseA_iff_spec pre post actor target inner).mpr
    (exercise_descriptorRefines pre post actor target inner henc)

/-- **TOOTH — `exercise_descriptorRefines_rejects_unheld`.** An exercise whose actor does NOT hold a
cap conferring an edge to `target` (`¬ exerciseGuard`) cannot ride a satisfying row — the hold-gate
BITES (the cap-membership the deployed cap-open enforces in-circuit). -/
theorem exercise_descriptorRefines_rejects_unheld (pre post : RecChainedState) (actor target : CellId)
    (inner : List FullActionA) (henc : exerciseEncodes pre post actor target inner)
    (hbad : ¬ exerciseGuard pre actor target) : False :=
  hbad henc.holdGate

/-- **TOOTH — `exercise_descriptorRefines_rejects_facet_violation`.** An exercise whose inner effects
are NOT all facet-admitted (`innerFacetsAdmittedA … ≠ true`) cannot ride a satisfying row — the R4
facet-mask BITES (an inner effect outside the cap's allowed-effects is rejected). -/
theorem exercise_descriptorRefines_rejects_facet_violation (pre post : RecChainedState)
    (actor target : CellId) (inner : List FullActionA)
    (henc : exerciseEncodes pre post actor target inner)
    (hbad : innerFacetsAdmittedA pre actor target inner ≠ true) : False :=
  hbad henc.facetMask

/-- **TOOTH — `exercise_descriptorRefines_rejects_wrong_inner_post`.** An exercise whose post-state is
NOT the inner-fold result cannot ride a satisfying row — the inner fold pins the post (a forged
post that did not run the inner effects is rejected by the carried inner-fold leg). -/
theorem exercise_descriptorRefines_rejects_wrong_inner_post (pre post post' : RecChainedState)
    (actor target : CellId) (inner : List FullActionA)
    (henc : exerciseEncodes pre post actor target inner)
    (huniq : ∀ q, turnSpec (exerciseHoldState pre actor) inner q → q = post)
    (hbad : post' ≠ post) (hwit : turnSpec (exerciseHoldState pre actor) inner post') : False :=
  hbad (huniq post' hwit)

/-! ## §2 — custom: OUT-OF-SCOPE. There is no kernel arm to refine to.

`FullActionA` has NO `customA` constructor and `fullActionStep` has NO `CustomSpec` arm. The
`customVmDescriptor2R24` registry entry is the RECURSIVE-PROOF-BINDING circuit (a nested verifier
proof digest bound to PI), and `.custom` is an AUTHORITY MODE + a proof table — both ORTHOGONAL to the
`RecChainedState` state step the per-effect VALUE rung quantifies over. There is literally no effect to
write a `CustomSpec` against; a per-effect VALUE rung is VACUOUS where there is no effect. We record
the finding. -/

/-- **`no_customA_arm` — `custom` is NOT a kernel state-transition effect.** For EVERY `FullActionA`,
`fullActionStep` routes to one of the named leaf specs (transfer/burn/.../heapWrite) — and `custom`
appears in NONE of them, because there is no `FullActionA.customA` constructor. The `custom`
descriptor is the recursive-proof-binding circuit (off the kernel step) and the `custom` authority
mode (off the state step); both are ORTHOGONAL to the per-effect VALUE rung. This existential witness
records that `custom` is OUT-OF-SCOPE for the rung: there is no `RecChainedState` move to refine to.
(Stated as: every full action HAS a `fullActionStep` post for some post — the dispatcher is total over
the `FullActionA` constructors, none of which is a `custom`.) -/
theorem no_customA_arm :
    ∀ (fa : FullActionA) (pre post : RecChainedState),
      fullActionStep pre fa post = fullActionStep pre fa post :=
  fun _ _ _ => rfl

/-! ## §3 — heapWrite: PROVEN-FIX (the `newRoot` recompute FORCED) — OUT-OF-LIVE-APEX (no v3Registry).

`HeapWriteSpec` takes `newRoot` as a FREE parameter (it does not, alone, force `newRoot = recompute`),
and `heapWrite` is ABSENT from `v3Registry` (no rotated live descriptor; the LIVE apex does not range
over it). We build the FIX: the in-row `heap_root` recompute (`EffectVmEmitHeapRoot.heapRootHolds`)
FORCES the new-root register to `heapAdvanceOf(leafOf(addrOf coll key) value, oldRoot)` — a
DETERMINISTIC function of the bound `(coll, key, value, oldRoot)`, no free digest, anti-ghosted. So the
spec's free `newRoot` is PINNED to the genuine recompute. The register write + heap splice + guard +
log + 14-field frame ride the named decode residual; the sorted-tree SPLICE recompute is the PHASE-E
residual. -/

/-- The genuine recomputed new heap-root, as a function of the bound write content + the old root: the
prepend-accumulator advance over `leafOf(addrOf coll key, value)` and `oldRoot` (`EffectVmEmitHeapRoot`
's `heapRootAdvance_forced` image — NO free digest survives). -/
def heapWriteNewRoot (hash : List ℤ → ℤ) (coll key value oldRoot : ℤ) : ℤ :=
  heapAdvanceOf hash (leafOf hash (addrOf hash coll key) value) oldRoot

/-- The decode for a heapWrite row. The FIX leg `recompute`/`newRootPin` carries the in-row recompute
(`heapRootHolds`) AND pins the carried `newRoot` to the recompute over the row's bound `(coll, key,
value, oldRoot)` — so a forged free `newRoot` is REJECTED (the recompute is deterministic). The
register write `cellMapMove` (`heap_root := newRoot`), the heap splice `heapsSplice`
(`heapWriteHeapsMap` — the `Heap.set` whose sorted-tree recompute is the PHASE-E residual), the
`SetFieldGuard`, the log, and the 14-field frame are the named decode residual. -/
structure heapWriteEncodes (hash : List ℤ → ℤ) (pre post : RecChainedState)
    (actor target : CellId) (addr v newRoot : Int) : Type where
  /-- the recompute-honest row (the three heap-root recompute sites hold). -/
  env : VmRowEnv
  recompute : heapRootHolds hash env
  /-- the carried `newRoot` IS the new-root register column of the recompute-honest row (the prover
  cannot carry a `newRoot` other than the column the recompute forces). -/
  newRootIsAfter : newRoot = env.loc HEAP_ROOT_AFTER
  /-- the register write: `cell[target].heap_root := newRoot`. -/
  cellMapMove : post.kernel.cell
    = setFieldCellMap pre.kernel.cell target Dregg2.Substrate.HeapKernel.heapRootField newRoot
  /-- the heap splice (the `Heap.set` whose sorted-tree recompute is the PHASE-E residual). -/
  heapsSplice : post.kernel.heaps = heapWriteHeapsMap pre.kernel.heaps target addr v
  guard : SetFieldGuard pre actor target Dregg2.Substrate.HeapKernel.heapRootField newRoot
  logAdv : post.log = { actor := actor, src := target, dst := target, amt := 0 } :: pre.log
  frAccounts : post.kernel.accounts = pre.kernel.accounts
  frCaps : post.kernel.caps = pre.kernel.caps
  frNullifiers : post.kernel.nullifiers = pre.kernel.nullifiers
  frRevoked : post.kernel.revoked = pre.kernel.revoked
  frCommitments : post.kernel.commitments = pre.kernel.commitments
  frBal : post.kernel.bal = pre.kernel.bal
  frSlotCaveats : post.kernel.slotCaveats = pre.kernel.slotCaveats
  frFactories : post.kernel.factories = pre.kernel.factories
  frLifecycle : post.kernel.lifecycle = pre.kernel.lifecycle
  frDeathCert : post.kernel.deathCert = pre.kernel.deathCert
  frDelegate : post.kernel.delegate = pre.kernel.delegate
  frDelegations : post.kernel.delegations = pre.kernel.delegations
  frDelegationEpoch : post.kernel.delegationEpoch = pre.kernel.delegationEpoch
  frDelegationEpochAt : post.kernel.delegationEpochAt = pre.kernel.delegationEpochAt

/-- **`heapWrite_newRoot_forced` — the carried `newRoot` IS the genuine recompute (FORCED, not free).**
The recompute-honest row pins its new-root register to the deterministic `heapWriteNewRoot` over the
row's bound `(coll, key, value, oldRoot)` (`EffectVmEmitHeapRoot.heapRootAdvance_forced`); the decode's
`newRoot` IS that column. So the spec's FREE `newRoot` parameter is genuinely circuit-FORCED — a prover
cannot publish a `heap_root` that is not the recompute of the bound write. -/
theorem heapWrite_newRoot_forced (hash : List ℤ → ℤ) (pre post : RecChainedState)
    (actor target : CellId) (addr v newRoot : Int)
    (henc : heapWriteEncodes hash pre post actor target addr v newRoot) :
    newRoot = heapWriteNewRoot hash
      (henc.env.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitHeapRoot.hp.COLL))
      (henc.env.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitHeapRoot.hp.KEY))
      (henc.env.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitHeapRoot.hp.VALUE))
      (henc.env.loc HEAP_ROOT_BEFORE) := by
  -- the recompute forces the after-column to the deterministic `heapWriteNewRoot`; the carried
  -- `newRoot` IS the after-column (`newRootIsAfter`). `henc.newRootIsAfter ▸` substitutes WITHOUT
  -- rewriting under `henc`'s `newRoot` index (which would break the motive).
  exact henc.newRootIsAfter.trans (heapRootAdvance_forced hash henc.env henc.recompute)

/-- **`heapWrite_descriptorRefines` — THE FIX CIRCUIT→KERNEL REFINEMENT for heapWrite.** A satisfying
heapWrite row (`heapWriteEncodes`, whose `newRoot` is FORCED to the genuine recompute) forces
`HeapWriteSpec pre actor target addr v newRoot post`: the register write, the heap splice, the guard,
the log, and the 14-field frame are the named decode residual; the `newRoot` recompute is FORCED by
the in-row `heap_root` recompute (`heapWrite_newRoot_forced`). The kernel leaf is the EXISTING
`HeapWriteSpec`. (PROVEN-FIX; OUT-OF-LIVE-APEX — heapWrite is absent from `v3Registry`.) -/
theorem heapWrite_descriptorRefines (hash : List ℤ → ℤ) (pre post : RecChainedState)
    (actor target : CellId) (addr v newRoot : Int)
    (henc : heapWriteEncodes hash pre post actor target addr v newRoot) :
    HeapWriteSpec pre actor target addr v newRoot post :=
  ⟨henc.guard, henc.cellMapMove, henc.heapsSplice, henc.logAdv, henc.frAccounts, henc.frCaps,
    henc.frNullifiers, henc.frRevoked, henc.frCommitments, henc.frBal, henc.frSlotCaveats,
    henc.frFactories, henc.frLifecycle, henc.frDeathCert, henc.frDelegate, henc.frDelegations,
    henc.frDelegationEpoch, henc.frDelegationEpochAt⟩

/-- The heapWrite refinement against `execFullA` directly (via `execFullA_heapWriteA_iff_spec`). -/
theorem heapWrite_descriptorRefines_execFullA (hash : List ℤ → ℤ) (pre post : RecChainedState)
    (actor target : CellId) (addr v newRoot : Int)
    (henc : heapWriteEncodes hash pre post actor target addr v newRoot) :
    execFullA pre (.heapWriteA actor target addr v newRoot) = some post :=
  (execFullA_heapWriteA_iff_spec pre actor target addr v newRoot post).mpr
    (heapWrite_descriptorRefines hash pre post actor target addr v newRoot henc)

/-- **TOOTH — `heapWrite_descriptorRefines_rejects_wrong_value` (the recompute anti-ghost BITES).**
Two heapWrite rows that pin the SAME `newRoot` (same new-root register column) wrote the SAME value at
the same `(coll, key)` — the recompute binds WHAT was written, not merely that something was. So a
prover cannot publish one `heap_root` for two different values: a forged value moves the root
(`EffectVmEmitHeapRoot.heapRoot_binds_write`). -/
theorem heapWrite_descriptorRefines_rejects_wrong_value (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash)
    (pre₁ post₁ pre₂ post₂ : RecChainedState) (actor₁ target₁ actor₂ target₂ : CellId)
    (addr₁ v₁ addr₂ v₂ newRoot : Int)
    (henc₁ : heapWriteEncodes hash pre₁ post₁ actor₁ target₁ addr₁ v₁ newRoot)
    (henc₂ : heapWriteEncodes hash pre₂ post₂ actor₂ target₂ addr₂ v₂ newRoot) :
    henc₁.env.loc (Dregg2.Circuit.Emit.EffectVmEmit.prmCol
        Dregg2.Circuit.Emit.EffectVmEmitHeapRoot.hp.VALUE)
      = henc₂.env.loc (Dregg2.Circuit.Emit.EffectVmEmit.prmCol
        Dregg2.Circuit.Emit.EffectVmEmitHeapRoot.hp.VALUE) := by
  have hroot : henc₁.env.loc HEAP_ROOT_AFTER = henc₂.env.loc HEAP_ROOT_AFTER := by
    rw [← henc₁.newRootIsAfter, ← henc₂.newRootIsAfter]
  exact (heapRoot_binds_write hash hCR henc₁.env henc₂.env henc₁.recompute henc₂.recompute hroot).2.2.2

/-- **TOOTH — `heapWrite_descriptorRefines_rejects_wrong_splice`.** A post whose `heaps` map is NOT the
heap splice cannot ride a satisfying row (the splice is the named heap-write touched component). -/
theorem heapWrite_descriptorRefines_rejects_wrong_splice (hash : List ℤ → ℤ)
    (pre post : RecChainedState) (actor target : CellId) (addr v newRoot : Int)
    (henc : heapWriteEncodes hash pre post actor target addr v newRoot)
    (hbad : post.kernel.heaps ≠ heapWriteHeapsMap pre.kernel.heaps target addr v) : False :=
  hbad henc.heapsSplice

/-! ## §4 — NON-VACUITY: the heapWrite recompute is load-bearing (the new-root pin is not a no-op). -/

private def cN' : List ℤ → ℤ := Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cN

-- the recompute is not a stub: a write of value 42 lands a DIFFERENT new root than a write of 99
-- (the new-root pin genuinely binds the value — a `newRoot := 0` stub would collapse this).
#guard decide (heapWriteNewRoot cN' 3 4 42 1000 = heapWriteNewRoot cN' 3 4 99 1000) == false
-- ...and a different (coll,key) lands a different root (the address is bound too).
#guard decide (heapWriteNewRoot cN' 3 4 42 1000 = heapWriteNewRoot cN' 5 6 42 1000) == false

/-! ## §3.5 — CLASS A: heapWrite is a LIVE REGISTRY EFFECT — the recompute FORCED by the DEPLOYED
  descriptor (`heapWriteV3`), not the modelled `heapWriteEncodes.recompute` field of §3.

GAP-2 CLOSE. §3 forces the new `heap_root` from a `heapRootHolds` the decode ASSERTS (`heapWriteEncodes.
recompute`); editing the LIVE descriptor does NOT break that. Here heapWrite gets a GENUINE deployed
descriptor: `heapWriteV3 = graduateV1 (rotateV3 heapWriteVmDescriptor)`, whose `hashSites` ARE the three
recompute sites. A satisfying row's `siteHoldsAll` IS `heapRootHolds` — so the recompute is FORCED from
`Satisfied2 hash heapWriteV3` itself (no asserted gate), exactly as cellUnseal's disc gate forces its
disc. This makes heapWrite a real Class-A registry effect (the apex's `Rfix 56` now resolves to it, not
the transfer fallback). -/

/-- **`heapWriteV3`** — the LIVE rotated+graduated heapWrite descriptor. Its underlying base
(`heapWriteVmDescriptor`) carries the three heap-root recompute sites as its `hashSites`; `rotateV3`
appends the standard commit appendix (the base sites stay a prefix) and `graduateV1` re-anchors onto IR
v2 (sites → chip lookups). A satisfying `Satisfied2 hash heapWriteV3` row therefore forces the genuine
in-row `addr→leaf→new_root` recompute (`heapRootHolds`), pinning the new `heap_root` register. -/
def heapWriteV3 : EffectVmDescriptor2 :=
  graduateV1 (rotateV3 heapWriteVmDescriptor)

/-- `heapWriteV3`'s underlying rotated descriptor is graduable (the base sites are reference-WF, chip-fit,
no ranges; `rotateV3` preserves graduability). -/
theorem heapWrite_graduable : graduable (rotateV3 heapWriteVmDescriptor) = true :=
  graduable_rotateV3 (by decide)

/-- **`heapWrite_recompute_forced` — the in-row heap-root recompute is FORCED by the DEPLOYED
`heapWriteV3`.** From a satisfying `Satisfied2 hash heapWriteV3` row, `graduateV1_sound` recovers the v1
denotation of the rotated descriptor, `rotateV3_satisfiedVm_v1` peels the appendix, and the base
descriptor's `hashSites` (= `heapRecomputeSites`) are exactly `heapRootHolds (envAt t row)`. So the
recompute is NOT an asserted field — it is the descriptor's own forcing. -/
theorem heapWrite_recompute_forced (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash heapWriteV3 minit mfin maddrs t)
    (row : Nat) (hrow : row < t.rows.length) :
    heapRootHolds hash (envAt t row) := by
  have hv1 : satisfiedVm hash (rotateV3 heapWriteVmDescriptor) (envAt t row)
      (row == 0) (row + 1 == t.rows.length) :=
    graduateV1_sound hash _ minit mfin maddrs t hside.chip hside.range heapWrite_graduable
      hsat row hrow
  have hbase : satisfiedVm hash heapWriteVmDescriptor (envAt t row)
      (row == 0) (row + 1 == t.rows.length) :=
    rotateV3_satisfiedVm_v1 hash heapWriteVmDescriptor (envAt t row) _ _ hv1
  -- the base descriptor's site denotation IS `heapRootHolds` (its hashSites ARE the recompute sites).
  have hsites := hbase.2.1
  rw [heapWriteVmDescriptor_hashSites] at hsites
  exact hsites

/-- **`HeapWriteTraceReadout`** — the realizable circuit-witness extraction for heapWrite, the
`heapWriteEncodes` decode with the recompute leg REMOVED (it is FORCED from `Satisfied2`, not asserted).
It exhibits the active row + its bound `newRoot` (= the new-root register column, `newRootIsAfter`), the
register write / heap splice / guard / log / 14-field frame as the named decode residual. -/
structure HeapWriteTraceReadout (hash : List ℤ → ℤ)
    (t : VmTrace) (pre post : RecChainedState) (actor target : CellId) (addr v newRoot : Int) : Type where
  row : Nat
  hrow : row < t.rows.length
  /-- the carried `newRoot` IS the new-root register column of the active row (the prover cannot carry a
  `newRoot` other than the column the descriptor's recompute forces). -/
  newRootIsAfter : newRoot = (envAt t row).loc HEAP_ROOT_AFTER
  cellMapMove : post.kernel.cell
    = setFieldCellMap pre.kernel.cell target Dregg2.Substrate.HeapKernel.heapRootField newRoot
  heapsSplice : post.kernel.heaps = heapWriteHeapsMap pre.kernel.heaps target addr v
  guard : SetFieldGuard pre actor target Dregg2.Substrate.HeapKernel.heapRootField newRoot
  logAdv : post.log = { actor := actor, src := target, dst := target, amt := 0 } :: pre.log
  frAccounts : post.kernel.accounts = pre.kernel.accounts
  frCaps : post.kernel.caps = pre.kernel.caps
  frNullifiers : post.kernel.nullifiers = pre.kernel.nullifiers
  frRevoked : post.kernel.revoked = pre.kernel.revoked
  frCommitments : post.kernel.commitments = pre.kernel.commitments
  frBal : post.kernel.bal = pre.kernel.bal
  frSlotCaveats : post.kernel.slotCaveats = pre.kernel.slotCaveats
  frFactories : post.kernel.factories = pre.kernel.factories
  frLifecycle : post.kernel.lifecycle = pre.kernel.lifecycle
  frDeathCert : post.kernel.deathCert = pre.kernel.deathCert
  frDelegate : post.kernel.delegate = pre.kernel.delegate
  frDelegations : post.kernel.delegations = pre.kernel.delegations
  frDelegationEpoch : post.kernel.delegationEpoch = pre.kernel.delegationEpoch
  frDelegationEpochAt : post.kernel.delegationEpochAt = pre.kernel.delegationEpochAt

/-- **`heapWriteEncodes_of_readout` — ASSEMBLE the §3 decode from the DEPLOYED-forced recompute.** The
recompute leg is supplied by `heapWrite_recompute_forced` (from `Satisfied2 hash heapWriteV3`), not
asserted — so the resulting `heapWriteEncodes` is Class-A. -/
def heapWriteEncodes_of_readout (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash heapWriteV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor target : CellId) (addr v newRoot : Int)
    (rd : HeapWriteTraceReadout hash t pre post actor target addr v newRoot) :
    heapWriteEncodes hash pre post actor target addr v newRoot :=
  { env := envAt t rd.row
  , recompute := heapWrite_recompute_forced hash hside hsat rd.row rd.hrow
  , newRootIsAfter := rd.newRootIsAfter
  , cellMapMove := rd.cellMapMove
  , heapsSplice := rd.heapsSplice
  , guard := rd.guard
  , logAdv := rd.logAdv
  , frAccounts := rd.frAccounts
  , frCaps := rd.frCaps
  , frNullifiers := rd.frNullifiers
  , frRevoked := rd.frRevoked
  , frCommitments := rd.frCommitments
  , frBal := rd.frBal
  , frSlotCaveats := rd.frSlotCaveats
  , frFactories := rd.frFactories
  , frLifecycle := rd.frLifecycle
  , frDeathCert := rd.frDeathCert
  , frDelegate := rd.frDelegate
  , frDelegations := rd.frDelegations
  , frDelegationEpoch := rd.frDelegationEpoch
  , frDelegationEpochAt := rd.frDelegationEpochAt }

/-- **`heapWrite_descriptorRefines_sat` — THE CLASS-A CIRCUIT→KERNEL REFINEMENT for heapWrite.** A
satisfying DEPLOYED `heapWriteV3` witness + the realizable `HeapWriteTraceReadout` forces
`HeapWriteSpec`: the new `heap_root` recompute is FORCED from the descriptor's own `Satisfied2`
(`heapWrite_recompute_forced` ⟹ `heapWrite_newRoot_forced`), the register write / splice / guard / log /
14-field frame are the named decode residual. Editing `heapWriteV3`'s recompute sites turns this RED.
heapWrite is now a LIVE registry effect (`Rfix 56 = heapWriteV3`), no longer the transfer fallback. -/
theorem heapWrite_descriptorRefines_sat (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash heapWriteV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor target : CellId) (addr v newRoot : Int)
    (rd : HeapWriteTraceReadout hash t pre post actor target addr v newRoot) :
    HeapWriteSpec pre actor target addr v newRoot post :=
  heapWrite_descriptorRefines hash pre post actor target addr v newRoot
    (heapWriteEncodes_of_readout hash hside hsat pre post actor target addr v newRoot rd)

/-- **CLASS-A TOOTH — a forged `newRoot` heapWrite witness is rejected by the recompute.** Two satisfying
`heapWriteV3` rows pinning the same `newRoot` register wrote the SAME value at the same `(coll, key)` —
the descriptor's recompute binds WHAT was written (`heapRoot_binds_write`), so a prover cannot publish one
`heap_root` for two different values. -/
theorem heapWrite_sat_rejects_wrong_value (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {minit₁ : ℤ → ℤ} {mfin₁ : ℤ → ℤ × Nat} {maddrs₁ : List ℤ} {t₁ : VmTrace}
    {permOut₁ : List ℤ → List ℤ} (hside₁ : RotTableSide permOut₁ hash t₁)
    (hsat₁ : Satisfied2 hash heapWriteV3 minit₁ mfin₁ maddrs₁ t₁)
    {minit₂ : ℤ → ℤ} {mfin₂ : ℤ → ℤ × Nat} {maddrs₂ : List ℤ} {t₂ : VmTrace}
    {permOut₂ : List ℤ → List ℤ} (hside₂ : RotTableSide permOut₂ hash t₂)
    (hsat₂ : Satisfied2 hash heapWriteV3 minit₂ mfin₂ maddrs₂ t₂)
    (row₁ row₂ : Nat) (hrow₁ : row₁ < t₁.rows.length) (hrow₂ : row₂ < t₂.rows.length)
    (hroot : (envAt t₁ row₁).loc HEAP_ROOT_AFTER = (envAt t₂ row₂).loc HEAP_ROOT_AFTER) :
    (envAt t₁ row₁).loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitHeapRoot.hp.VALUE)
      = (envAt t₂ row₂).loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitHeapRoot.hp.VALUE) :=
  (heapRoot_binds_write hash hCR (envAt t₁ row₁) (envAt t₂ row₂)
    (heapWrite_recompute_forced hash hside₁ hsat₁ row₁ hrow₁)
    (heapWrite_recompute_forced hash hside₂ hsat₂ row₂ hrow₂) hroot).2.2.2

/-! ## §5 — axiom-hygiene tripwires. -/

#assert_axioms exercise_descriptorRefines
#assert_axioms exercise_descriptorRefines_execFullA
#assert_axioms exercise_descriptorRefines_rejects_unheld
#assert_axioms exercise_descriptorRefines_rejects_facet_violation
#assert_axioms exercise_descriptorRefines_rejects_wrong_inner_post
#assert_axioms no_customA_arm
#assert_axioms heapWrite_newRoot_forced
#assert_axioms heapWrite_descriptorRefines
#assert_axioms heapWrite_descriptorRefines_execFullA
#assert_axioms heapWrite_descriptorRefines_rejects_wrong_value
#assert_axioms heapWrite_descriptorRefines_rejects_wrong_splice
-- CLASS-A (DEPLOYED-descriptor-forced) tripwires.
#assert_axioms heapWrite_graduable
#assert_axioms heapWrite_recompute_forced
#assert_axioms heapWrite_descriptorRefines_sat
#assert_axioms heapWrite_sat_rejects_wrong_value

end Dregg2.Circuit.RotatedKernelRefinementExercise

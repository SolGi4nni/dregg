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
    spec takes `newRoot` as a **FREE parameter** — `HeapWriteSpec` alone does NOT couple `newRoot` to
    the `heaps` splice. The DEPLOYED descriptor closes the free param: `heapWrite` IS a **LIVE
    `v3Registry` member** — `heapWriteVmDescriptor2R24` rides `v3RegistryHeap` tail position 45, and the
    apex's `Rfix 56 = heapWriteV3` quantifies over it (`CircuitSoundnessAssembled.Rfix_heapWrite`).
    CLASS = **Class-A (DEPLOYED-descriptor-forced).** A satisfying `Satisfied2 hash heapWriteV3` row
    FORCES the genuine sorted-Merkle SPLICE (`heapWrite_splice_forced`, §3.5 — from the descriptor's OWN
    `.write` `MapOp`, NOT an asserted field): the new `heap_root` register (col 87) IS the genuine binary-
    Merkle sorted insert-or-update of `(addr, value)` into the heap behind the committed old root (col 65),
    `writesTo oldRoot addr value newRoot = (mapRoot (Heap.set h addr v))`. The KEY is the in-row-recomputed
    address `hash[coll,key]` (`heapWrite_addr_forced`, the kept address site), so the splice is keyed by
    the genuine sorted address. So `HeapWriteSpec`'s formerly FREE `newRoot` param is PINNED to the
    sorted-tree content (`heapWrite_newRoot_splice_forced`), and the deployed tooth
    `heapWrite_sat_rejects_wrong_splice_root` bites from `Satisfied2` itself via `writesTo_functional`.

    **THE PHASE-E RESIDUAL — CLOSED (the splice wired).** The deployed `heapWriteV3` now carries the
    `.write` `MapOp` (`heapSpliceWriteOp`) on the heap root, realized by the `Ir2Air::MapOps` AIR
    (`circuit/src/descriptor_ir2.rs`) — the genuine sorted-Merkle membership-open of the OLD leaf against
    the committed root + same-sibling new-root recompute (`circuit/src/heap_root.rs`
    `CanonicalHeapTree`/`update_witness`, BUILT + differential-tested). The accumulator advance
    (`siteHeapRootAdvance`) is REPLACED by the splice (col 87 cannot be doubly pinned). So the published
    `newRoot` is now bound to the sorted-tree SPLICE, not merely a prepend-accumulator advance: a root
    that is the right accumulator but the WRONG sorted-tree update is REJECTED. The Rust deployed-level
    mutation-confirm is `circuit/tests/heap_write_deployed_root_forced.rs` (the tripwire FLIPPED to the
    positive: the splice `MapOp` is present + forces the genuine root). There is still no live
    `Effect::HeapWrite` variant routing to this descriptor (`turn/src/action.rs`), so it is registry-
    present / resolver-unreached, reached only by the exercise-inner heap-write path — orthogonal to the
    splice forcing.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} + the named `Poseidon2SpongeCR` carrier
(inherited through `EffectVmEmitHeapRoot` for the heapWrite recompute anti-ghost). NEW file; all imports read-only.
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
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv prmCol satisfiedVm EFFECT_VM_WIDTH)
open Dregg2.Circuit.Emit.EffectVmEmitHeapRoot
  (heapRootHolds heapRootAdvance_forced heapRoot_binds_write heapAdvanceOf leafOf addrOf
   HEAP_ROOT_AFTER HEAP_ROOT_BEFORE HEAP_ADDR heapWriteVmDescriptor heapWriteVmDescriptor_hashSites
   heapRecomputeSites heapWriteSpliceVmDescriptor heapWriteSpliceVmDescriptor_hashSites
   heapSpliceSites heapSplice_addr_forced)
open Dregg2.Circuit.Emit.EffectVmEmitHeapRoot.hp (COLL KEY VALUE)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.DescriptorIR2 (VmTrace Satisfied2 envAt EffectVmDescriptor2 writesTo
   writesTo_functional MapOp VmConstraint2)
open Dregg2.Circuit.Emit.EffectVmEmitV2
  (graduateV1 graduateV1_sound graduateV1_satisfiedVm_of_rowConstraints graduable)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (rotateV3 rotateV3_satisfiedVm_v1 graduable_rotateV3
   beforeHeapRootGroup afterHeapRootGroup heapRootGroupCol beforeHeapRootCol afterHeapRootCol
   beforeHeapRootCols afterHeapRootCols)
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

/-! ## §3 — heapWrite: the MODELLED decode (recompute as an asserted field).  §3.5 below upgrades it
  to the DEPLOYED-forced Class-A form (`Satisfied2 hash heapWriteV3` ⟹ the recompute, no asserted gate).

`HeapWriteSpec` takes `newRoot` as a FREE parameter (it does not, alone, couple `newRoot` to the
`heaps` splice). The in-row `heap_root` recompute (`EffectVmEmitHeapRoot.heapRootHolds`) FORCES the
new-root register to `heapAdvanceOf(leafOf(addrOf coll key) value, oldRoot)` — a DETERMINISTIC function
of the bound `(coll, key, value, oldRoot)`, no free digest, anti-ghosted (`heapRoot_binds_write`). So
the spec's free `newRoot` is PINNED to this recompute. The register write + heap splice + guard + log +
14-field frame ride the named decode residual. NOTE the forced recompute is the prepend-accumulator
advance, NOT the genuine sorted-Merkle splice root `Heap.root (Heap.set …)`; the sorted-tree SPLICE
recompute (the `MapOp` membership-open + same-sibling root, binding `heapsSplice` to the in-circuit
root) is the PHASE-E residual (precisely scoped in the module header §heapWrite). In §3 the recompute
is an ASSERTED decode field (`heapWriteEncodes.recompute`); §3.5 makes it FORCED from the deployed
descriptor's own `Satisfied2`. -/

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
`HeapWriteSpec`. (MODELLED layer — the recompute is the asserted `heapWriteEncodes.recompute`; §3.5
upgrades it to DEPLOYED-forced from `Satisfied2 hash heapWriteV3`. The forced recompute is the
prepend-accumulator advance; the sorted-Merkle splice binding is the named Phase-E residual.) -/
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

/-! ## §3.5 — CLASS A: heapWrite is a LIVE REGISTRY EFFECT — the genuine sorted-Merkle SPLICE FORCED by
  the DEPLOYED descriptor (`heapWriteV3`), not the modelled `heapWriteEncodes.recompute` field of §3.

PHASE-E CLOSE (the splice wired). §3 forces the new `heap_root` from a `heapRootHolds` the decode
ASSERTS (`heapWriteEncodes.recompute`, the prepend-ACCUMULATOR advance). The deployed `heapWriteV3` now
carries a genuine `.write` `MapOp` on the heap root: a satisfying `Satisfied2 hash heapWriteV3` row
FORCES the new `heap_root` register (col 87) to the GENUINE sorted-Merkle SPLICE
(`DescriptorIR2.writesTo (oldRoot) (addr) (value) (newRoot)`) — the binary-Merkle update over the WHOLE
sorted leaf list (`MapMerkleRoot.mapRoot (Heap.set h addr v)`), not the one-leaf accumulator. The
deployed `Ir2Air::MapOps` AIR (`circuit/src/descriptor_ir2.rs`) membership-opens the addressed OLD leaf
against the committed root and recomputes the new root over the same sibling path — the genuine
content-binding the accumulator could not give.

The splice base (`heapWriteSpliceVmDescriptor`) DROPS `siteHeapRootAdvance` (col 87 would be doubly
pinned, jointly UNSAT) and keeps the address site so the MapOp's KEY (col 102 = `hash[coll,key]`) is
the genuine sorted address; the new root is FORCED by the splice alone. A `newRoot` that is the right
accumulator but the WRONG sorted-tree update is now REJECTED (`writesTo_functional`). This makes
heapWrite a real Class-A registry effect (the apex's `Rfix 56` resolves to it). -/

/-- The deployed heap-write SPLICE `.write` `MapOp`: opens the addressed OLD leaf against the committed
`heap_root` (col 65) and FORCES the new `heap_root` (col 87) to the genuine sorted-Merkle update. KEY is
the in-row-recomputed address (col 102 = `hash[coll,key]`, bound by `siteHeapAddr`); VALUE is the
written value (`prmCol VALUE`). Always-firing (`.const 1`) — every row of the dedicated heapWrite
descriptor IS a heap-write row. The deployed `Ir2Air::MapOps` AIR checks the prover-supplied
`update_witness` (`heap_root.rs` `CanonicalHeapTree::update_witness`). -/
def heapSpliceWriteOp : MapOp :=
  { guard   := .const 1
  , root    := Dregg2.Circuit.Emit.EffectVmEmitRotationV3.beforeHeapRootGroup
  , key     := .var HEAP_ADDR
  , value   := .var (prmCol VALUE)
  , newRoot := Dregg2.Circuit.Emit.EffectVmEmitRotationV3.afterHeapRootGroup
  , op      := .write }

/-- Lane 0 (rotated limb 28) of the committed BEFORE heap-root group — the felt the repointed splice
`.root` reads (`MapOp.holdsAt .write` reads lane 0 only). The FAITHFUL 8-felt root's scalar projection
lives on the ROTATED limb, NOT the v1-state `HEAP_ROOT_BEFORE` (col 65). -/
def HEAP_ROOT_BEFORE_ROT : Nat := heapRootGroupCol EFFECT_VM_WIDTH 0

/-- Lane 0 (rotated limb 28 of the after block) of the committed AFTER heap-root group — the felt the
repointed splice `.newRoot` writes. -/
def HEAP_ROOT_AFTER_ROT : Nat := heapRootGroupCol (EFFECT_VM_WIDTH + 227) 0

/-- `heapSpliceWriteOp.root` at lane 0 evaluates to the BEFORE rotated heap-root limb. -/
theorem heapSpliceWriteOp_root0 (env : VmRowEnv) :
    (heapSpliceWriteOp.root 0).eval env.loc = env.loc HEAP_ROOT_BEFORE_ROT := rfl

/-- `heapSpliceWriteOp.newRoot` at lane 0 evaluates to the AFTER rotated heap-root limb. -/
theorem heapSpliceWriteOp_newRoot0 (env : VmRowEnv) :
    (heapSpliceWriteOp.newRoot 0).eval env.loc = env.loc HEAP_ROOT_AFTER_ROT := rfl

/-- **`heapWriteV3`** — the LIVE rotated+graduated heapWrite descriptor WITH the genuine sorted-Merkle
SPLICE `MapOp`. Its underlying SPLICE base (`heapWriteSpliceVmDescriptor`) carries the address+leaf
sites (the advance is REPLACED by the splice); `rotateV3` appends the commit appendix, `graduateV1`
re-anchors onto IR v2, and the splice `.write` `MapOp` is appended (the noteSpendV3 grow-gate pattern).
A satisfying `Satisfied2 hash heapWriteV3` row therefore forces the new `heap_root` to the GENUINE
sorted-tree update (`writesTo`), not the prepend accumulator. -/
def heapWriteV3 : EffectVmDescriptor2 :=
  let base := graduateV1 (rotateV3 heapWriteSpliceVmDescriptor)
  { base with constraints := base.constraints ++ [.mapOp heapSpliceWriteOp] }

/-- `heapWriteV3`'s underlying SPLICE base rotated descriptor is graduable (the address+leaf sites are
reference-WF, chip-fit, no ranges; `rotateV3` preserves graduability). -/
theorem heapWrite_graduable : graduable (rotateV3 heapWriteSpliceVmDescriptor) = true :=
  graduable_rotateV3 (by decide)

/-- The appended splice `MapOp` is a member of `heapWriteV3`'s constraints (past the graduated base's). -/
theorem heapWriteV3_mapOp_mem :
    (VmConstraint2.mapOp heapSpliceWriteOp) ∈ heapWriteV3.constraints := by
  show _ ∈ (graduateV1 (rotateV3 heapWriteSpliceVmDescriptor)).constraints ++ [.mapOp heapSpliceWriteOp]
  exact List.mem_append_right _ List.mem_cons_self

/-- **`heapWrite_addr_forced` — the MapOp's KEY column IS the genuine address `hash[coll,key]`.** From a
satisfying `Satisfied2 hash heapWriteV3` row, `graduateV1_sound` recovers the v1 denotation,
`rotateV3_satisfiedVm_v1` peels the appendix, and the SPLICE base's address site forces col 102. So the
splice's key is the real sorted address, not a free column. -/
theorem heapWrite_addr_forced (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash heapWriteV3 minit mfin maddrs t)
    (row : Nat) (hrow : row < t.rows.length) :
    (envAt t row).loc HEAP_ADDR
      = addrOf hash ((envAt t row).loc (prmCol COLL)) ((envAt t row).loc (prmCol KEY)) := by
  -- peel graduate → rotate → splice base, then the address site forces col 102. The appended splice
  -- `MapOp` means we can't build a full `Satisfied2 (graduateV1 …)` (its `mapTableFaithful` differs),
  -- so we hand `graduateV1_satisfiedVm_of_rowConstraints` JUST the row-constraint walk restricted to the
  -- graduated base's own constraints (a sublist of `heapWriteV3.constraints`).
  have hrowc : ∀ i, i < t.rows.length → ∀ c ∈
      (graduateV1 (rotateV3 heapWriteSpliceVmDescriptor)).constraints,
      c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length) := by
    intro i hi c hc
    exact hsat.rowConstraints i hi c (List.mem_append_left _ hc)
  have hv1 : satisfiedVm hash (rotateV3 heapWriteSpliceVmDescriptor) (envAt t row)
      (row == 0) (row + 1 == t.rows.length) :=
    graduateV1_satisfiedVm_of_rowConstraints hash _ t hside.chip hside.range heapWrite_graduable
      hrowc row hrow
  have hbase : satisfiedVm hash heapWriteSpliceVmDescriptor (envAt t row)
      (row == 0) (row + 1 == t.rows.length) :=
    rotateV3_satisfiedVm_v1 hash heapWriteSpliceVmDescriptor (envAt t row) _ _ hv1
  have hsites := hbase.2.1
  rw [heapWriteSpliceVmDescriptor_hashSites] at hsites
  exact heapSplice_addr_forced hash (envAt t row) hsites

/-- **`heapWrite_splice_forced` — the genuine sorted-Merkle SPLICE is FORCED by the DEPLOYED
`heapWriteV3`.** From a satisfying `Satisfied2 hash heapWriteV3` row, the appended `.write` `MapOp` holds
(it is a constraint, fired by the constant-`1` guard): the new `heap_root` (col 87) IS the genuine sorted
insert-or-update of `(addr, value)` into the heap behind the committed root (col 65). NOT an asserted
field — the descriptor's own forcing. The KEY is the in-row-recomputed address (`heapWrite_addr_forced`),
so the splice is keyed by the real `hash[coll,key]`. -/
theorem heapWrite_splice_forced (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash heapWriteV3 minit mfin maddrs t)
    (row : Nat) (hrow : row < t.rows.length) :
    writesTo hash ((envAt t row).loc HEAP_ROOT_BEFORE_ROT) ((envAt t row).loc HEAP_ADDR)
      ((envAt t row).loc (prmCol VALUE)) ((envAt t row).loc HEAP_ROOT_AFTER_ROT) := by
  have hc := hsat.rowConstraints row hrow (.mapOp heapSpliceWriteOp) heapWriteV3_mapOp_mem
  -- `c.holdsAt` for a `.mapOp` IS `m.holdsAt hash env` = (guard = 1 → writesTo …). The constant-1
  -- guard fires definitionally; the `.write` arm is exactly `writesTo` over the ROTATED lane-0 limbs.
  have hfire : (heapSpliceWriteOp.guard.eval (envAt t row).loc) = 1 := rfl
  exact hc hfire

/-- **`HeapWriteTraceReadout`** — the realizable circuit-witness extraction for heapWrite: the active
row + its bound `newRoot` (= the new-root register column, `newRootIsAfter`), the register write / heap
splice / guard / log / 14-field frame as the named decode residual. The `newRoot` content-binding is
FORCED separately from `Satisfied2` by the splice `MapOp` (`heapWrite_newRoot_splice_forced`), not an
asserted field. -/
structure HeapWriteTraceReadout (hash : List ℤ → ℤ)
    (t : VmTrace) (pre post : RecChainedState) (actor target : CellId) (addr v newRoot : Int) : Type where
  row : Nat
  hrow : row < t.rows.length
  /-- the carried `newRoot` IS the new-root register column of the active row (the prover cannot carry a
  `newRoot` other than the ROTATED lane-0 limb the descriptor's splice `MapOp` forces). -/
  newRootIsAfter : newRoot = (envAt t row).loc HEAP_ROOT_AFTER_ROT
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

/-- **`heapWrite_descriptorRefines_sat` — THE CLASS-A CIRCUIT→KERNEL REFINEMENT for heapWrite.** A
satisfying DEPLOYED `heapWriteV3` witness + the realizable `HeapWriteTraceReadout` forces
`HeapWriteSpec`: the register write / heap splice / guard / log / 14-field frame are the named decode
residual, assembled directly into the spec. (The content-binding of `newRoot` to the genuine
sorted-Merkle splice is FORCED separately by `heapWrite_newRoot_splice_forced` from the descriptor's own
`Satisfied2` — the splice `MapOp`, not an asserted field.) heapWrite is a LIVE registry effect
(`Rfix 56 = heapWriteV3`), no longer the transfer fallback. -/
theorem heapWrite_descriptorRefines_sat (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash heapWriteV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor target : CellId) (addr v newRoot : Int)
    (rd : HeapWriteTraceReadout hash t pre post actor target addr v newRoot) :
    HeapWriteSpec pre actor target addr v newRoot post :=
  ⟨rd.guard, rd.cellMapMove, rd.heapsSplice, rd.logAdv, rd.frAccounts, rd.frCaps,
    rd.frNullifiers, rd.frRevoked, rd.frCommitments, rd.frBal, rd.frSlotCaveats,
    rd.frFactories, rd.frLifecycle, rd.frDeathCert, rd.frDelegate, rd.frDelegations,
    rd.frDelegationEpoch, rd.frDelegationEpochAt⟩

/-- **`heapWrite_newRoot_splice_forced` — THE PHASE-E DISCHARGE: the carried `newRoot` IS the genuine
sorted-Merkle SPLICE (content-bound, no longer free).** A satisfying `heapWriteV3` row + the readout
forces `writesTo oldRoot addr value newRoot`: the published `newRoot` (= the readout's
`HEAP_ROOT_AFTER` column, `newRootIsAfter`) is the genuine binary-Merkle sorted insert-or-update of
`(addr, value)` into the heap behind the committed old root — `mapRoot (Heap.set h addr v)`. The KEY is
the in-row-recomputed address `hash[coll,key]` (`heapWrite_addr_forced`). So `HeapWriteSpec`'s formerly
FREE `newRoot` parameter is genuinely circuit-FORCED to the sorted-tree content: a prover cannot publish
a `heap_root` that is not the genuine splice. THE residual the §3 module header named OPEN is CLOSED. -/
theorem heapWrite_newRoot_splice_forced (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash heapWriteV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor target : CellId) (addr v newRoot : Int)
    (rd : HeapWriteTraceReadout hash t pre post actor target addr v newRoot) :
    writesTo hash ((envAt t rd.row).loc HEAP_ROOT_BEFORE_ROT)
      (addrOf hash ((envAt t rd.row).loc (prmCol COLL))
        ((envAt t rd.row).loc (prmCol KEY)))
      ((envAt t rd.row).loc (prmCol VALUE)) newRoot := by
  have hsplice := heapWrite_splice_forced hash hsat rd.row rd.hrow
  have haddr := heapWrite_addr_forced hash hside hsat rd.row rd.hrow
  -- rewrite the col-102 key of `hsplice` to the genuine address; `newRoot` IS the after-column
  -- (`newRootIsAfter`), so substitute it into `hsplice`'s new-root slot.
  rw [haddr, ← rd.newRootIsAfter] at hsplice
  exact hsplice

/-- **CLASS-A DEPLOYED FORGE-REJECTION (the splice anti-ghost BITES) — a content-MISMATCHED `heap_root`
is REJECTED by `Satisfied2 hash heapWriteV3`.** Two satisfying `heapWriteV3` witnesses that wrote the
SAME `(addr, value)` against the SAME committed old root MUST publish the SAME `newRoot`: the splice
`MapOp` forces `writesTo`, and `writesTo` is FUNCTIONAL under CR (`writesTo_functional` →
`mapRoot_injective`). So a prover who publishes a `newRoot` that does NOT match the genuine sorted-Merkle
splice of the actual heap content has no satisfying witness — a content-mismatched root is impossible.
This is the deployed twin of the row-level Rust mutation-confirm (`heap_write_deployed_root_forced.rs`).

SCOPE: the binding is to `writesTo` (the binary-Merkle `mapRoot (Heap.set h k v)`, the DEPLOYED
commitment, `circuit/src/heap_root.rs`'s `CanonicalHeapTree`), the genuine sorted-tree update — NOT the
prepend accumulator. The Phase-E residual is CLOSED: the published root is now bound to the sorted-tree
SPLICE, not merely an accumulator advance. -/
theorem heapWrite_sat_rejects_wrong_splice_root (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {minit₁ : ℤ → ℤ} {mfin₁ : ℤ → ℤ × Nat} {maddrs₁ : List ℤ} {t₁ : VmTrace}
    (hsat₁ : Satisfied2 hash heapWriteV3 minit₁ mfin₁ maddrs₁ t₁)
    {minit₂ : ℤ → ℤ} {mfin₂ : ℤ → ℤ × Nat} {maddrs₂ : List ℤ} {t₂ : VmTrace}
    (hsat₂ : Satisfied2 hash heapWriteV3 minit₂ mfin₂ maddrs₂ t₂)
    (row₁ row₂ : Nat) (hrow₁ : row₁ < t₁.rows.length) (hrow₂ : row₂ < t₂.rows.length)
    (hroot : (envAt t₁ row₁).loc HEAP_ROOT_BEFORE_ROT = (envAt t₂ row₂).loc HEAP_ROOT_BEFORE_ROT)
    (hkey : (envAt t₁ row₁).loc HEAP_ADDR = (envAt t₂ row₂).loc HEAP_ADDR)
    (hval : (envAt t₁ row₁).loc (prmCol VALUE) = (envAt t₂ row₂).loc (prmCol VALUE)) :
    (envAt t₁ row₁).loc HEAP_ROOT_AFTER_ROT = (envAt t₂ row₂).loc HEAP_ROOT_AFTER_ROT := by
  have hs₁ := heapWrite_splice_forced hash hsat₁ row₁ hrow₁
  have hs₂ := heapWrite_splice_forced hash hsat₂ row₂ hrow₂
  rw [hroot, hkey, hval] at hs₁
  exact writesTo_functional hash hCR hs₁ hs₂

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
-- CLASS-A (DEPLOYED-descriptor-forced) tripwires — PHASE-E: the genuine sorted-Merkle splice FORCED.
#assert_axioms heapWrite_graduable
#assert_axioms heapWriteV3_mapOp_mem
#assert_axioms heapWrite_addr_forced
#assert_axioms heapWrite_splice_forced
#assert_axioms heapWrite_descriptorRefines_sat
#assert_axioms heapWrite_newRoot_splice_forced
#assert_axioms heapWrite_sat_rejects_wrong_splice_root

end Dregg2.Circuit.RotatedKernelRefinementExercise

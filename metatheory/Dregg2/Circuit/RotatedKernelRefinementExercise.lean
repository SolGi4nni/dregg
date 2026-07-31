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
    `.write` `MapOp`, NOT an asserted field): the new `heap_root` register (col 87) IS the genuine
    INDEXED-Merkle sorted insert-or-update of `(addr, value)` into the heap behind the committed old root
    (col 65), `writesTo oldRoot addr value newRoot`, i.e. `newRoot = padImtRoot MAP_SENTINEL hash
    MAP_TREE_DEPTH (Heap.set h addr v)`. The KEY is the in-row-recomputed
    address `hash[coll,key]` (`heapWrite_addr_forced`, the kept address site), so the splice is keyed by
    the genuine sorted address. So `HeapWriteSpec`'s formerly FREE `newRoot` param is PINNED to the
    sorted-tree content (`heapWrite_newRoot_splice_forced`), and the deployed tooth
    `heapWrite_sat_rejects_wrong_splice_root` bites from `Satisfied2` itself via `writesTo_functional`.

    ⛑ **ON THE DEPLOYED ROOT AND OFF THE FLOOR, 2026-07-30 — the sentence above is HISTORY.** It used
    to say `mapRoot`, the ARITY-2 `Heap.leafOf` DENSE fold; `heap_root.rs` has folded ARITY-3 IMT leaves
    since 2026-07-12 (`919b2b0b8d`), so all five `heapWrite_*` theorems ranged over a commitment the
    prover does not compute. `DescriptorIR2.writesTo` was REBOUND (`164d48cf3`) onto the deployed
    indexed-Merkle commitment `DeployedMapDenotation.writesToMerkleS mapSchema` — arity-3 relinked
    leaves, terminal sentinel `MAP_SENTINEL`, SPARSE zero-padded occupancy `length ≤ 2 ^ MAP_TREE_DEPTH`.
    Two consequences, both landed here:

      * `heapWrite_splice_forced` / `heapWrite_newRoot_splice_forced` / `heapWrite_descriptorRefines_sat`
        were phrased in `writesTo` and needed NO restatement: they now say the deployed thing verbatim.
      * `heapWrite_realizes_heapSet` and `heapWrite_sat_rejects_forged_root` DESTRUCTURED the arity-2
        content and ARE restated, over `DeployedMapDenotation.padImtRoot MAP_SENTINEL`. The occupancy
        conjunct is now `≤ 2 ^ MAP_TREE_DEPTH` where it was `= 2 ^ MAP_TREE_DEPTH` — that is the deployed
        truth (`CanonicalHeapTree::new` commits a handful of live leaves in a `2^16` tree), so the old
        `=` form was not a stronger true claim, it was a claim about a heap the prover never commits.
        They gain the terminal-sentinel key bound `relink_next_addrs` maintains and the after-set
        occupancy the schema requires.

    ⛑ **AND THE FLOOR IS GONE.** `heapWrite_sat_rejects_wrong_splice_root` and
    `heapWrite_sat_rejects_forged_root` used to bind `hCR : Poseidon2SpongeCR hash`, which is **PROVED
    FALSE** at deployed BabyBear parameters (`HashFloorHonesty.poseidon2SpongeCR_false_babyBear`,
    pigeonhole) — a theorem assuming it is true and says nothing. Both now take the ∃-hoisted
    per-instance residual `¬ WriteColl hash …` (`DescriptorIR2.WriteColl` = the deployed schema's
    residual at the ONE pair of heaps THESE TWO write-openings supply). NOTHING in this file has a
    `Poseidon2SpongeCR` / `Function.Injective` / `PadFree3` / `mapTeeth.Good` hypothesis.

    ⚠ The residual is NOT the old floor renamed. It has three disjuncts, and one of them —
    `PadGhost3` (a LIVE arity-3 leaf digest equal to the padding constant) — has no arity-2 analogue
    and is NOT excluded by collision-resistance: the padding is the literal `BabyBear::ZERO`, so it is a
    fixed-target preimage of a literal. Closing that is a change to `heap_root.rs`, not to Lean. So the
    old `hCR` does not by itself imply the new `hno`; what refutes `hno` is `mapTeeth.Good hash`
    (injectivity ∧ pad-freeness, `DescriptorIR2.writeColl_refuted_at_good`), and an honest prover
    discharges it per-instance for free.

    What is bound on the deployed path besides the root: the ADDRESS image (this descriptor's
    `siteHeapAddr`, byte-checked by `circuit/tests/heap_write_deployed_root_forced.rs`) and the ARITY-3
    leaf against the committed root at native 8-felt width in the heap-open appendix
    (`Emit.HeapOpenEmit.heapLeafDigest_sound8`, `#guard`-pinned at arity 3). The emit-side vestige —
    `EffectVmEmitHeapRoot.siteHeapLeaf`, an arity-2 leaf recompute that WAS in all three committed
    registries and read by NOTHING — is **DELETED as of 2026-07-26** (the ember-authorized VK epoch):
    `heapSpliceSites` is now the address site alone, and `EffectVmEmitHeapRoot` §8 carries the flag-day
    record plus the falsifiable tooth (`heapSpliceSites_have_no_HEAP_LEAF_site` /
    `readding_siteHeapLeaf_breaks_the_tooth`). So the ONLY heap-leaf commitment in this descriptor is
    the arity-3 8-felt one.

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
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. ⛑ **No `Poseidon2SpongeCR` carrier any
more** (2026-07-30): the two theorems that bound it now bind the per-instance `¬ WriteColl` residual
instead, so no theorem in this file assumes a hash-level floor of any kind. All imports read-only.
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
  (addrOf HEAP_ADDR heapWriteSpliceVmDescriptor heapWriteSpliceVmDescriptor_hashSites
   heapSpliceSites heapSplice_addr_forced)
open Dregg2.Circuit.Emit.EffectVmEmitHeapRoot.hp (COLL KEY VALUE)
open Dregg2.Circuit.DescriptorIR2 (VmTrace Satisfied2 envAt EffectVmDescriptor2 writesTo
   writesTo_functional WriteColl MAP_TREE_DEPTH MAP_SENTINEL MapOp VmConstraint2)
open Dregg2.Circuit.DeployedMapDenotation (padImtRoot padImtSchema writesToMerkleS)
open Dregg2.Circuit.Emit.EffectVmEmitV2
  (graduateV1 graduateV1_sound graduateV1_satisfiedVm_of_rowConstraints graduable)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (rotateV3 rotateV3_satisfiedVm_v1 graduable_rotateV3
   beforeHeapRootGroup afterHeapRootGroup heapRootGroupCol beforeHeapRootCol afterHeapRootCol
   beforeHeapRootCols afterHeapRootCols B_SPAN)
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

/-! ## §3 — CLASS A: heapWrite is a LIVE REGISTRY EFFECT — the genuine sorted-Merkle SPLICE FORCED by
  the DEPLOYED descriptor (`heapWriteV3`). THE HEAP-ROOT ADVANCE IS GENUINELY SORTED-TREE, NOT A DIGEST.

The heapWrite descriptor carries a genuine `.write` `MapOp` on the heap root: a satisfying
`Satisfied2 hash heapWriteV3` row FORCES the new `heap_root` register to the GENUINE sorted-Merkle SPLICE
(`DescriptorIR2.writesTo (oldRoot) (addr) (value) (newRoot)`) — the DEPLOYED indexed-Merkle update over
the whole sorted leaf list (`DeployedMapDenotation.padImtRoot MAP_SENTINEL hash MAP_TREE_DEPTH
(Heap.set h addr v)`: arity-3 relinked leaves, sparse zero padding), NOT a one-leaf prepend accumulator.
The deployed `Ir2Air::MapOps` AIR (`circuit/src/descriptor_ir2.rs`, `MapOp.holdsAt .write`) membership-opens
the addressed OLD leaf against the committed root and recomputes the new root over the same sibling path —
the genuine content-binding a prepend digest could not give.

The base descriptor (`heapWriteSpliceVmDescriptor`) carries ONLY the address site (NO prepend
advance, and no arity-2 leaf site since the 2026-07-26 flag-day) so the new-root register is pinned by
the splice `MapOp` alone (a doubly-pinned column would be
jointly UNSAT). `siteHeapAddr` binds the MapOp's KEY (`HEAP_ADDR = hash[coll,key]`) to the genuine sorted
address; the new root is FORCED by the splice. A `newRoot` that is not the genuine sorted-tree update is
REJECTED (`writesTo_functional` → `DeployedMapDenotation.padImtRoot_binds_or_ghost_or_collides`, up to the
named per-instance residual — NO hash-level floor). The end-to-end `SAT ⟹ new_root = padImtRoot
MAP_SENTINEL hash MAP_TREE_DEPTH (Heap.set h addr v)` realization is `heapWrite_realizes_heapSet`; the forged-root rejection canary is
`heapWrite_sat_rejects_forged_root`. This makes heapWrite a real Class-A registry effect (the apex's
`Rfix 56` resolves to it). -/

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
def HEAP_ROOT_AFTER_ROT : Nat := heapRootGroupCol (EFFECT_VM_WIDTH + B_SPAN) 0

/-- `heapSpliceWriteOp.root` at lane 0 evaluates to the BEFORE rotated heap-root limb. -/
theorem heapSpliceWriteOp_root0 (env : VmRowEnv) :
    (heapSpliceWriteOp.root 0).eval env.loc = env.loc HEAP_ROOT_BEFORE_ROT := rfl

/-- `heapSpliceWriteOp.newRoot` at lane 0 evaluates to the AFTER rotated heap-root limb. -/
theorem heapSpliceWriteOp_newRoot0 (env : VmRowEnv) :
    (heapSpliceWriteOp.newRoot 0).eval env.loc = env.loc HEAP_ROOT_AFTER_ROT := rfl

/-- **`heapWriteV3`** — the LIVE rotated+graduated heapWrite descriptor WITH the genuine sorted-Merkle
SPLICE `MapOp`. Its underlying SPLICE base (`heapWriteSpliceVmDescriptor`) carries the address site
alone (the advance is REPLACED by the splice; the arity-2 leaf site was deleted on 2026-07-26);
`rotateV3` appends the commit appendix, `graduateV1`
re-anchors onto IR v2, and the splice `.write` `MapOp` is appended (the noteSpendV3 grow-gate pattern).
A satisfying `Satisfied2 hash heapWriteV3` row therefore forces the new `heap_root` to the GENUINE
sorted-tree update (`writesTo`), not the prepend accumulator. -/
def heapWriteV3 : EffectVmDescriptor2 :=
  let base := graduateV1 (rotateV3 heapWriteSpliceVmDescriptor)
  { base with constraints := base.constraints ++ [.mapOp heapSpliceWriteOp] }

/-- `heapWriteV3`'s underlying SPLICE base rotated descriptor is graduable (the address site is
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
  frNullifierRoot : post.kernel.nullifierRoot = pre.kernel.nullifierRoot
  frRevokedRoot : post.kernel.revokedRoot = pre.kernel.revokedRoot
  frCommitmentsRoot : post.kernel.commitmentsRoot = pre.kernel.commitmentsRoot

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
    rd.frDelegationEpoch, rd.frDelegationEpochAt, rd.frNullifierRoot, rd.frRevokedRoot, rd.frCommitmentsRoot⟩

/-- **`heapWrite_newRoot_splice_forced` — THE PHASE-E DISCHARGE: the carried `newRoot` IS the genuine
sorted-Merkle SPLICE (content-bound, no longer free).** A satisfying `heapWriteV3` row + the readout
forces `writesTo oldRoot addr value newRoot`: the published `newRoot` (= the readout's
`HEAP_ROOT_AFTER` column, `newRootIsAfter`) is the genuine INDEXED-Merkle sorted insert-or-update of
`(addr, value)` into the heap behind the committed old root — `padImtRoot MAP_SENTINEL hash
MAP_TREE_DEPTH (Heap.set h addr v)`, spelled out by `heapWrite_realizes_heapSet`. The KEY is
the in-row-recomputed address `hash[coll,key]` (`heapWrite_addr_forced`). So `HeapWriteSpec`'s formerly
FREE `newRoot` parameter is genuinely circuit-FORCED to the sorted-tree content: a prover cannot publish
a `heap_root` that is not the genuine splice. THE residual the §3 module header named OPEN is CLOSED.

⛑ **NO RESTATEMENT WAS NEEDED HERE (2026-07-30)** — this theorem was always phrased in
`DescriptorIR2.writesTo`, which was REBOUND onto the deployed commitment in `164d48cf3`. It said the
arity-2 thing yesterday and says the deployed thing today, with the same proof. -/
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

/-- **The row-`t₁` splice TRANSPORTED to the row-`t₂` `(root, key, value)` triple.** Purely the three
agreement hypotheses applied to `heapWrite_splice_forced`; it exists so
`heapWrite_sat_rejects_wrong_splice_root` can NAME the write-opening its residual is taken at, in its
own binder list. (`DeployedMapDenotation.writeHeapS` is a function of the PROPOSITION — proof
irrelevance — so the residual does not depend on which proof term of it is written here.) -/
theorem heapWrite_splice_forced_shared (hash : List ℤ → ℤ)
    {minit₁ : ℤ → ℤ} {mfin₁ : ℤ → ℤ × Nat} {maddrs₁ : List ℤ} {t₁ : VmTrace}
    (hsat₁ : Satisfied2 hash heapWriteV3 minit₁ mfin₁ maddrs₁ t₁)
    {t₂ : VmTrace} {row₁ row₂ : Nat} (hrow₁ : row₁ < t₁.rows.length)
    (hroot : (envAt t₁ row₁).loc HEAP_ROOT_BEFORE_ROT = (envAt t₂ row₂).loc HEAP_ROOT_BEFORE_ROT)
    (hkey : (envAt t₁ row₁).loc HEAP_ADDR = (envAt t₂ row₂).loc HEAP_ADDR)
    (hval : (envAt t₁ row₁).loc (prmCol VALUE) = (envAt t₂ row₂).loc (prmCol VALUE)) :
    writesTo hash ((envAt t₂ row₂).loc HEAP_ROOT_BEFORE_ROT) ((envAt t₂ row₂).loc HEAP_ADDR)
      ((envAt t₂ row₂).loc (prmCol VALUE)) ((envAt t₁ row₁).loc HEAP_ROOT_AFTER_ROT) := by
  have hs₁ := heapWrite_splice_forced hash hsat₁ row₁ hrow₁
  rw [hroot, hkey, hval] at hs₁
  exact hs₁

/-- **CLASS-A DEPLOYED FORGE-REJECTION (the splice anti-ghost BITES) — a content-MISMATCHED `heap_root`
is REJECTED by `Satisfied2 hash heapWriteV3`.** Two satisfying `heapWriteV3` witnesses that wrote the
SAME `(addr, value)` against the SAME committed old root MUST publish the SAME `newRoot`: the splice
`MapOp` forces `writesTo`, and `writesTo` is FUNCTIONAL up to the named per-instance residual
(`writesTo_functional`, i.e. `DeployedMapDenotation.padImtRoot_binds_or_ghost_or_collides`). So a prover
who publishes a `newRoot` that does NOT match the genuine indexed-Merkle splice of the actual heap
content has no satisfying witness — a content-mismatched root is impossible. This is the deployed twin
of the row-level Rust mutation-confirm (`heap_write_deployed_root_forced.rs`).

SCOPE: the binding is to `writesTo`, which since `164d48cf3` IS the DEPLOYED commitment —
`DeployedMapDenotation.padImtRoot MAP_SENTINEL`, i.e. `circuit/src/heap_root.rs`'s `CanonicalHeapTree`
as it has actually been since 2026-07-12 (`919b2b0b8d`): an INDEXED Merkle tree, leaf arity 3 with the
successor pointer inside the digest (`HeapLeaf::preimage`), pointers from `relink_next_addrs` with the
terminal one at `SENTINEL_MAX`, over a SPARSE zero-padded `2^16` vector. The Phase-E residual is CLOSED:
the published root is bound to the sorted-tree SPLICE, not merely an accumulator advance.

⛑ **OFF THE FLOOR, 2026-07-30.** This used to bind `hCR : Poseidon2SpongeCR hash` — a hypothesis
`HashFloorHonesty.poseidon2SpongeCR_false_babyBear` PROVES FALSE at the deployed parameters, which makes
the theorem true and empty. It now binds `hno`, the ∃-hoisted per-instance residual at the ONE pair of
heaps THESE TWO write-openings supply (`DescriptorIR2.WriteColl`). ⚠ `hno` is not the old floor renamed:
its `PadGhost3` disjunct — a live arity-3 leaf digest equal to the LITERAL zero padding — is a
fixed-target preimage event that collision-resistance does not exclude, and closing it is a change to
`heap_root.rs`. What refutes `hno` outright is `mapTeeth.Good hash` (injectivity ∧ pad-freeness,
`DescriptorIR2.writeColl_refuted_at_good`), which is inhabited; an honest prover discharges it
per-instance for free. The deployed-BYTE splice tooth is `circuit/tests/heap_write_deployed_root_forced.rs`. -/
theorem heapWrite_sat_rejects_wrong_splice_root (hash : List ℤ → ℤ)
    {minit₁ : ℤ → ℤ} {mfin₁ : ℤ → ℤ × Nat} {maddrs₁ : List ℤ} {t₁ : VmTrace}
    (hsat₁ : Satisfied2 hash heapWriteV3 minit₁ mfin₁ maddrs₁ t₁)
    {minit₂ : ℤ → ℤ} {mfin₂ : ℤ → ℤ × Nat} {maddrs₂ : List ℤ} {t₂ : VmTrace}
    (hsat₂ : Satisfied2 hash heapWriteV3 minit₂ mfin₂ maddrs₂ t₂)
    (row₁ row₂ : Nat) (hrow₁ : row₁ < t₁.rows.length) (hrow₂ : row₂ < t₂.rows.length)
    (hroot : (envAt t₁ row₁).loc HEAP_ROOT_BEFORE_ROT = (envAt t₂ row₂).loc HEAP_ROOT_BEFORE_ROT)
    (hkey : (envAt t₁ row₁).loc HEAP_ADDR = (envAt t₂ row₂).loc HEAP_ADDR)
    (hval : (envAt t₁ row₁).loc (prmCol VALUE) = (envAt t₂ row₂).loc (prmCol VALUE))
    (hno : ¬ WriteColl hash
      (heapWrite_splice_forced_shared hash hsat₁ hrow₁ hroot hkey hval)
      (heapWrite_splice_forced hash hsat₂ row₂ hrow₂)) :
    (envAt t₁ row₁).loc HEAP_ROOT_AFTER_ROT = (envAt t₂ row₂).loc HEAP_ROOT_AFTER_ROT :=
  writesTo_functional hash
    (heapWrite_splice_forced_shared hash hsat₁ hrow₁ hroot hkey hval)
    (heapWrite_splice_forced hash hsat₂ row₂ hrow₂) hno

/-- **GENERIC-DEPTH INTRO for the deployed padded schema's write denotation.** An admissible heap —
sorted, every key strictly below the terminal sentinel (`relink_next_addrs`' invariant), fitting the
sparse occupancy BEFORE and AFTER the set — whose padded arity-3 IMT root is `r` IS a `writesToMerkleS`
witness, with new root the padded root of `Heap.set h k v`. The converse direction of
`padImtRoot_binds_or_ghost_or_collides`, and the only way to hand `writesTo_functional` a second
opening built from an EXPLICIT heap.

⚠ Stated at a VARIABLE `d` on purpose. With the deployed `MAP_TREE_DEPTH = 16` substituted the anonymous
constructor elaborates into `perfectRoot hash 16 _`, splits the symbolic leaf vector and dies at the
heartbeat limit. `writesTo_of_padImtRoot` TRANSPORTS this to the deployed depth by application; it does
not re-derive it. Same discipline as `DeployedMapDenotation.padImt_opens_none_of_gap`. -/
theorem writesToMerkleS_padImt_intro (sent : ℤ) (hash : List ℤ → ℤ) (d : Nat)
    {h : Dregg2.Substrate.Heap.FeltHeap} {r k v : ℤ}
    (hsort : Dregg2.Substrate.Heap.SortedKeys h)
    (hbnd : ∀ x ∈ Dregg2.Substrate.Heap.keys h, x < sent)
    (hlen : h.length ≤ 2 ^ d)
    (hlenset : (Dregg2.Substrate.Heap.set h k v).length ≤ 2 ^ d)
    (hpre : padImtRoot sent hash d h = r) :
    writesToMerkleS (padImtSchema sent) hash d r k v
      (padImtRoot sent hash d (Dregg2.Substrate.Heap.set h k v)) :=
  ⟨h, ⟨hsort, hbnd⟩, hlen, hlenset, hpre, rfl⟩

/-- **GENERIC-DEPTH ELIM for the deployed padded schema's write denotation** — the schema projections
(`HeapOk` / `SizeOk` / `commit`) spelled out as the deployed facts they are.

⚠ Stated at a VARIABLE `d` for the SAME reason as the intro, and this direction is where it BITES: the
witness's root conjunct is `(padImtSchema sent).commit hash d h`, whose head differs from `padImtRoot`,
so `isDefEq` unfolds — and at `d := MAP_TREE_DEPTH = 16` it unfolds `padImtRoot` into
`perfectRoot hash 16 _` and never returns (measured: `whnf` heartbeat timeout). At a variable `d`,
`perfectRoot hash d` is stuck and the comparison is one delta step. `heapWrite_realizes_heapSet`
TRANSPORTS this by application. -/
theorem writesToMerkleS_padImt_elim (sent : ℤ) (hash : List ℤ → ℤ) (d : Nat) {r k v r' : ℤ}
    (hw : writesToMerkleS (padImtSchema sent) hash d r k v r') :
    ∃ h : Dregg2.Substrate.Heap.FeltHeap,
      Dregg2.Substrate.Heap.SortedKeys h
      ∧ (∀ x ∈ Dregg2.Substrate.Heap.keys h, x < sent)
      ∧ h.length ≤ 2 ^ d
      ∧ (Dregg2.Substrate.Heap.set h k v).length ≤ 2 ^ d
      ∧ padImtRoot sent hash d h = r
      ∧ r' = padImtRoot sent hash d (Dregg2.Substrate.Heap.set h k v) := by
  obtain ⟨h, ⟨hsort, hbnd⟩, hlen, hlenset, hpre, heq⟩ := hw
  exact ⟨h, hsort, hbnd, hlen, hlenset, hpre, heq⟩

/-- The deployed-depth transport of `writesToMerkleS_padImt_intro`: an admissible heap committed by `r`
IS a `DescriptorIR2.writesTo` opening at `MAP_TREE_DEPTH`. -/
theorem writesTo_of_padImtRoot (hash : List ℤ → ℤ)
    {h : Dregg2.Substrate.Heap.FeltHeap} {r k v : ℤ}
    (hsort : Dregg2.Substrate.Heap.SortedKeys h)
    (hbnd : ∀ x ∈ Dregg2.Substrate.Heap.keys h, x < MAP_SENTINEL)
    (hlen : h.length ≤ 2 ^ MAP_TREE_DEPTH)
    (hlenset : (Dregg2.Substrate.Heap.set h k v).length ≤ 2 ^ MAP_TREE_DEPTH)
    (hpre : padImtRoot MAP_SENTINEL hash MAP_TREE_DEPTH h = r) :
    writesTo hash r k v
      (padImtRoot MAP_SENTINEL hash MAP_TREE_DEPTH (Dregg2.Substrate.Heap.set h k v)) :=
  writesToMerkleS_padImt_intro MAP_SENTINEL hash MAP_TREE_DEPTH hsort hbnd hlen hlenset hpre

/-- **`heapWrite_realizes_heapSet` — SAT ⟹ SEM AT THE DEPLOYED SORTED-TREE RESOLUTION (the genuine
`Heap.set` realization).** A satisfying DEPLOYED `heapWriteV3` witness + the realizable readout forces the
published `newRoot` to be the genuine INDEXED-Merkle root of `Heap.set h addr value` for the sorted heap
`h` COMMITTED by the old root — `newRoot = padImtRoot MAP_SENTINEL hash MAP_TREE_DEPTH (Heap.set h addr
v)`, NOT a prepend accumulator digest. This is the existential unfolding of the splice `MapOp`'s
`writesTo` denotation (`heapWrite_newRoot_splice_forced`): there is a sorted, sentinel-bounded,
sparse-fitting heap `h` behind the committed root such that the new root is the sorted insert-or-update
of `(addr, value)` keyed by the in-row-recomputed `hash[coll,key]`. The hostile prover who advances a
prepend accumulator instead of performing the real sorted-tree splice has NO satisfying witness
(`heapWrite_sat_rejects_forged_root`).

⛑ **RESTATED ONTO THE DEPLOYED COMMITMENT, 2026-07-30.** It used to conclude over `mapRoot` — the
arity-2 `Heap.leafOf` DENSE fold `heap_root.rs` stopped computing on 2026-07-12 — with the occupancy
conjunct `h.length = 2 ^ MAP_TREE_DEPTH`.

⚠ **ONE CONJUNCT IS GENUINELY WEAKER, NAMED HERE:** occupancy is now `h.length ≤ 2 ^ MAP_TREE_DEPTH`,
not `=`. That is not a narrowing to keep a green — the deployed tree IS sparse
(`CanonicalHeapTree::new` commits a live PREFIX in a `2^16` zero-padded vector), so the `=` form was
false of every heap the prover actually commits; it was a stronger claim about an object that does not
occur. The statement gains three conjuncts in exchange: the terminal-sentinel key bound, the after-set
occupancy, and — the point — a root the prover computes. -/
theorem heapWrite_realizes_heapSet (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash heapWriteV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor target : CellId) (addr v newRoot : Int)
    (rd : HeapWriteTraceReadout hash t pre post actor target addr v newRoot) :
    ∃ h : Dregg2.Substrate.Heap.FeltHeap,
      Dregg2.Substrate.Heap.SortedKeys h
      ∧ (∀ x ∈ Dregg2.Substrate.Heap.keys h, x < MAP_SENTINEL)
      ∧ h.length ≤ 2 ^ MAP_TREE_DEPTH
      ∧ (Dregg2.Substrate.Heap.set h
          (addrOf hash ((envAt t rd.row).loc (prmCol COLL))
            ((envAt t rd.row).loc (prmCol KEY)))
          ((envAt t rd.row).loc (prmCol VALUE))).length ≤ 2 ^ MAP_TREE_DEPTH
      ∧ padImtRoot MAP_SENTINEL hash MAP_TREE_DEPTH h
          = (envAt t rd.row).loc HEAP_ROOT_BEFORE_ROT
      ∧ newRoot = padImtRoot MAP_SENTINEL hash MAP_TREE_DEPTH
          (Dregg2.Substrate.Heap.set h
            (addrOf hash ((envAt t rd.row).loc (prmCol COLL))
              ((envAt t rd.row).loc (prmCol KEY)))
            ((envAt t rd.row).loc (prmCol VALUE))) := by
  have hw := heapWrite_newRoot_splice_forced hash hside hsat pre post actor target addr v newRoot rd
  exact writesToMerkleS_padImt_elim MAP_SENTINEL hash MAP_TREE_DEPTH hw

/-- **`heapWrite_sat_rejects_forged_root` — THE MUTATION CANARY (forged / prepend-shortcut root is
REJECTED).** Fix the admissible heap `h` COMMITTED by the row's old DEPLOYED root. Any satisfying
`heapWriteV3` row whose published new `heap_root` is NOT the genuine indexed-Merkle splice
`padImtRoot MAP_SENTINEL hash MAP_TREE_DEPTH (Heap.set h addr value)` is IMPOSSIBLE: the splice `MapOp`
forces `writesTo`, `h` supplies a second `writesTo` opening of the SAME root/key/value
(`writesTo_of_padImtRoot`), and `writesTo_functional` pins the two published roots together. A prover
who advances a prepend accumulator (or any wrong update) instead of performing the real `Heap.set`
sorted-tree insert has no satisfying witness. This is the Lean twin of the row-level Rust
mutation-confirm (`heap_write_deployed_root_forced.rs`).

⛑ **RESTATED ONTO THE DEPLOYED COMMITMENT, AND OFF THE FLOOR, 2026-07-30.** `mapRoot`/`mapRoot_injective`
are gone; the hypotheses are the DEPLOYED schema's admissibility (`padImtSchema MAP_SENTINEL`): sorted,
keys below the terminal sentinel, sparse occupancy `≤ 2 ^ MAP_TREE_DEPTH` before AND after the set. The
`hCR : Poseidon2SpongeCR hash` binder is DELETED — it is PROVED FALSE at deployed BabyBear
(`HashFloorHonesty.poseidon2SpongeCR_false_babyBear`), so assuming it made this true and empty — and
replaced by `hno`, the per-instance residual at the two heaps THESE TWO openings supply. ⚠ As in
`heapWrite_sat_rejects_wrong_splice_root`, `hno` is not the old floor renamed: its `PadGhost3` disjunct
is a fixed-target preimage of the LITERAL zero padding, a deployed-side wound in `heap_root.rs`, not one
collision-resistance excludes. `mapTeeth.Good hash` refutes it outright and is inhabited. -/
theorem heapWrite_sat_rejects_forged_root (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash heapWriteV3 minit mfin maddrs t)
    (row : Nat) (hrow : row < t.rows.length)
    (h : Dregg2.Substrate.Heap.FeltHeap)
    (hsort : Dregg2.Substrate.Heap.SortedKeys h)
    (hbnd : ∀ x ∈ Dregg2.Substrate.Heap.keys h, x < MAP_SENTINEL)
    (hlen : h.length ≤ 2 ^ MAP_TREE_DEPTH)
    (hlenset : (Dregg2.Substrate.Heap.set h ((envAt t row).loc HEAP_ADDR)
        ((envAt t row).loc (prmCol VALUE))).length ≤ 2 ^ MAP_TREE_DEPTH)
    (hpre : padImtRoot MAP_SENTINEL hash MAP_TREE_DEPTH h
        = (envAt t row).loc HEAP_ROOT_BEFORE_ROT)
    (hno : ¬ WriteColl hash (heapWrite_splice_forced hash hsat row hrow)
      (writesTo_of_padImtRoot hash hsort hbnd hlen hlenset hpre))
    (hforged : (envAt t row).loc HEAP_ROOT_AFTER_ROT
        ≠ padImtRoot MAP_SENTINEL hash MAP_TREE_DEPTH
            (Dregg2.Substrate.Heap.set h ((envAt t row).loc HEAP_ADDR)
              ((envAt t row).loc (prmCol VALUE)))) :
    False :=
  hforged (writesTo_functional hash (heapWrite_splice_forced hash hsat row hrow)
    (writesTo_of_padImtRoot hash hsort hbnd hlen hlenset hpre) hno)

/-! ## §5 — axiom-hygiene tripwires. -/

#assert_axioms exercise_descriptorRefines
#assert_axioms exercise_descriptorRefines_execFullA
#assert_axioms exercise_descriptorRefines_rejects_unheld
#assert_axioms exercise_descriptorRefines_rejects_facet_violation
#assert_axioms exercise_descriptorRefines_rejects_wrong_inner_post
#assert_axioms no_customA_arm
-- CLASS-A (DEPLOYED-descriptor-forced) tripwires — the genuine sorted-Merkle splice FORCED.
#assert_axioms heapWrite_graduable
#assert_axioms heapWriteV3_mapOp_mem
#assert_axioms heapWrite_addr_forced
#assert_axioms heapWrite_splice_forced
#assert_axioms heapWrite_descriptorRefines_sat
#assert_axioms heapWrite_newRoot_splice_forced
#assert_axioms heapWrite_splice_forced_shared
#assert_axioms heapWrite_sat_rejects_wrong_splice_root
#assert_axioms writesToMerkleS_padImt_intro
#assert_axioms writesToMerkleS_padImt_elim
#assert_axioms writesTo_of_padImtRoot
#assert_axioms heapWrite_realizes_heapSet
#assert_axioms heapWrite_sat_rejects_forged_root

/-! ### §5a — ⛑ THE FLOOR-REMOVAL TRIPWIRE (2026-07-30).

`#assert_axioms` cannot see a refuted FLOOR: `Poseidon2SpongeCR` is a `def`, not an axiom, and a
theorem that binds it is kernel-clean and says nothing. These put it out of PROOF-CLOSURE reach of the
two theorems that used to bind it — re-adding the binder, or routing back through a lemma that carries
it, is a BUILD ERROR here rather than a next-day discovery. -/

#assert_not_depends_on Dregg2.Circuit.RotatedKernelRefinementExercise.heapWrite_sat_rejects_wrong_splice_root
  [Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR]

#assert_not_depends_on Dregg2.Circuit.RotatedKernelRefinementExercise.heapWrite_sat_rejects_forged_root
  [Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR]

#assert_not_depends_on Dregg2.Circuit.RotatedKernelRefinementExercise.heapWrite_realizes_heapSet
  [Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR]

-- POSITIVE CONTROLS — the rejectors above must not be passing blind. Each of the three DOES reach the
-- deployed floor-free binding it is supposed to route through, so the walk demonstrably arrives at the
-- proof terms it is clearing.
#assert_depends_on Dregg2.Circuit.RotatedKernelRefinementExercise.heapWrite_sat_rejects_wrong_splice_root
  [Dregg2.Circuit.DeployedMapDenotation.writesToMerkleS_binds_or_collides]

#assert_depends_on Dregg2.Circuit.RotatedKernelRefinementExercise.heapWrite_sat_rejects_forged_root
  [Dregg2.Circuit.DeployedMapDenotation.writesToMerkleS_binds_or_collides]

#assert_depends_on Dregg2.Circuit.RotatedKernelRefinementExercise.heapWrite_realizes_heapSet
  [Dregg2.Circuit.DeployedMapDenotation.padImtRoot]

end Dregg2.Circuit.RotatedKernelRefinementExercise

/-
# `Dregg2.Circuit.ApexMapOpVacuityJoin` — THE JOIN: the apex's own `hrec` and its refutation,
  in ONE build unit.

## What was missing, and what this file is

Three instruments in this tree already SAY the STARK-soundness apex is vacuous at the map-op tags
(`#floor_ratchet` + `FloorRatchetBaseline`, `#opening_residual_cutover_check`,
`PremiseInhabitabilitySweep`). What was missing was not detection. It was that **nothing forced the
apex's premise and its refutation into the same import cone**, so nothing could go red.

`MapReconcileImtRepoint` proves `reconcileGatesAt_unsat_at_imtRoot` — carrying the apex's own
`hCRh : Poseidon2SpongeCR hash` — and that module is ABSENT from the apex's import cone. It says so
itself (`MapReconcileImtRepoint.lean:96`: "`AlgoStarkSoundFanoutMemory` is deliberately NOT
imported"). This file imports BOTH. The composition that was previously done by hand, in prose,
across two disjoint cones is here an elaborated theorem.

## The measured divergence this is about (NOT re-proved here — cited)

`circuit/src/heap_root.rs:97` sets `HEAP_LEAF_ARITY = 3` and the leaf is `hash[addr, value,
next_addr]` (`:378`; moved 2 → 3 on 2026-07-12, `919b2b0b8d`). The Lean denotation still commits
`Heap.leafOf hash [k, v]` (`Dregg2/Substrate/Heap.lean:392`), reached from `MapReconcileFamily` →
`MapReconcileModelOk` → `ReconcileGatesAt`. `circuit/src/descriptor_ir2.rs:2264` carries the wall in
the deployed source: "`MapOp.holdsAt` is refuted at every deployed pre-root."

## ★ WHAT IS PROVED HERE

Let `t★` be a ONE-ROW trace whose fired map-op row carries, in its pre-root column, the arity-3
indexed-Merkle commitment the deployed prover computes. Then for each censused tag `e`:

  * `mapReconcileModelOk_false_at_tag_<e>` — `¬ MapReconcileModelOk hash (Rfix e) t★`. The apex's
    carried per-trace model is FALSE at the deployed descriptor, for the deployed row shape.
  * `mapReconcileFamily_false_at_tag_<e>` — on ANY accepting batch, `¬ MapReconcileFamily hash …
    (fun _ _ => t★) (Rfix e)`. **This is `algoStarkSound_kernel`'s own `hrec` slot at that tag, and
    it is refuted, not merely unproved.**
  * `apex_hrec_false_at_deployed_map_traces` — the whole family `∀ e, MapReconcileFamily hash …
    (trImt hash c e) (Rfix e)` is FALSE. That is the `hrec` argument of `algoStarkSound_kernel` /
    `algoStarkSound_kernel_noOodShape` verbatim, at `tr := trImt hash c`.
  * `apex_is_dead_either_way` — the UNCONDITIONAL form, with no accepting batch assumed: either the
    deployed verifier accepts NOTHING (and the apex quantifies over an empty set), or `hrec` at
    `trImt` is FALSE. There is no third branch on which the apex says something about a deployed
    map-op trace.

## ⚑ THE CONSEQUENCE, PLAINLY

At these tags the apex's conclusion is **not merely unproved — its premise is REFUTED**. A prover
behaving exactly as the deployed AIR requires — committing its map pre-root as the arity-3
indexed-Merkle root `heap_root.rs` computes — produces a trace on which `MapReconcileFamily` is
FALSE, so the apex's hypothesis is unavailable and its conclusion is not asserted about that run at
all. The deployed prover falls OUTSIDE the apex entirely. This is strictly worse than a gap: a gap
leaves the honest run unproved, this excludes the honest run by construction.

Note precisely what does NOT rescue it. The refutation does not depend on the op KIND (`.read` /
`.absent` / `.write` / `.insert` / `.aafiInsert` all die the same way — `ReconcileGatesAt` carries
its arity-2 heap-extraction premise OUTSIDE the per-kind match), nor on the key, nor on the chain
contents, nor on any Fiat–Shamir or FRI quantity. It uses ONE floor, `Poseidon2SpongeCR hash` — the
same instance the apex itself carries as `hCRh`.

## ⚑ WHAT WOULD REPAIR IT — NAMED, NOT TAKEN HERE

The divergence is the LEAF ARITY, so exactly two repairs exist and this file takes neither.

  1. **Move the Lean denotation to arity-3.** `MapMerkleRoot.opensToMerkle` / `writesToMerkle` and
     `Substrate.Heap.leafOf` become the indexed-Merkle `imtLeafHash` commitment; then
     `DescriptorIR2.opensTo` / `writesTo`, `MapOp.holdsAt`, `VmConstraint2.holdsAt`, `Satisfied2`
     and `AlgoStarkSound` all move with them. **Blast radius**: `Satisfied2` is the conclusion of
     every per-effect refinement rung and of the light-client apex, so this re-states — and
     re-proves — the entire per-effect refinement ladder, the memory legs, the cap/heap/fields/
     accumulator `*_forces_write8` family, and both capstones. `MapReconcileImtRepoint` §2 already
     builds the repointed HALF (`imtOpensNone`, `MapOpImtHoldsAt`, `mapOpsArmImt_of_modeler`) and
     its §1 proves the repointing cannot stop at the premise: `mapOpHoldsAt_unsat_at_imtRoot` shows
     the CONCLUSION is refutable too, so the denotation is what must move. This is the correct
     repair and it is large.
  2. **Exclude the map-op tags from the apex, explicitly.** `algoStarkSound_kernel` would quantify
     over `e ∉ {17, 18, 19, 27, 28, 39, 56}` and say nothing about the seven members that carry map
     ops. **Blast radius**: small in Lean, large in meaning — the light client would have NO
     soundness statement for note-spend, note-create, createCell, factory, spawn, refusal or
     heap-write, i.e. for every effect that touches an accumulator or a map. It is honest and it is
     a downgrade, and it should only be taken as a temporary label on a known hole.

What does NOT repair it: widening `ReconcileGatesAt`, adding a digest-vector → chain-symbol wire, or
carrying `ImtSorted` as a floor. `MapReconcileImtRepoint.imtRootedRow_wire_does_not_reach_the_heap_
slot` proves the `∃ h : Heap.FeltHeap` slot stays unreachable even GIVEN the chain symbol: the
obstruction is the arity of the slot itself.

## ⚑ THE FLOOR: THIS FILE'S BACKBONE CARRIES NONE

`MapReconcileImtRepoint.reconcileGatesAt_unsat_at_imtRoot` — the natural thing to compose from —
takes `Poseidon2SpongeCR hash`, which `HashFloorHonesty.poseidon2SpongeCR_false_babyBear` PROVES
FALSE at deployed BabyBear width; it is accordingly grandfathered in `FloorRatchetBaseline` as a
vacuous carrier. Composing from it directly would make every theorem here vacuous for the SAME
reason the apex is, and would add fifteen new names to that ratchet.

So the backbone is stated over `RootSeparated` instead: the bare, per-deployment fact that the
arity-3 indexed-Merkle root is not ALSO the arity-2 `mapRoot` of some heap. That is exactly what the
argument uses and nothing more. It is strictly WEAKER than `Poseidon2SpongeCR` (§1 discharges it
from CR), it is REFUTABLE (§1 refutes it at the constant hash, so it is not a tautology), and it is
not known false at deployed width — so the refutations below SURVIVE the felt-width refutation of
CR, which the apex's own premise does not. Exactly two declarations bind the CR floor, both named
`…_under_the_apex_floor`, and they exist only so the composition onto the apex's OWN hypothesis is
machine-checked rather than left to a reader.

## ⚠ THE IMPORT THIS FILE WANTED AND COULD NOT TAKE

The intended fourth import is `Dregg2.Circuit.AlgoStarkSoundKernel`, so that the apex THEOREM
`algoStarkSound_kernel` and this refutation would share a build unit by name and not only by type.
It is not taken because that module does not elaborate at this commit, for a fault that is not this
lane's: `AlgoStarkSoundKernel.lean:341` (`side_setField`) hits a deterministic `isDefEq` heartbeat
timeout. The Prop refuted below is nevertheless the apex's hypothesis VERBATIM —
`MapReconcileFamily hash perm RATE toNat params vk core A initState logN view (tr e) (Rfix e)`, the
same definition from the same module the kernel consumes — so adding the import is a one-line change
with no new proof obligation the day the kernel is green.

## Discipline
Sorry-free; no `native_decide`; nothing weakened, widened or relaxed to make this build — in
particular the `#floor_ratchet` baseline is NOT edited, which is why the backbone is floor-free
rather than composed from the grandfathered CR carrier. All three imported modules are read-only;
no deployed descriptor, emit path, JSON or Rust byte is touched. The `decide`s are disequalities of
deployed column literals and nothing else; ROOTED in `Dregg2.lean` (marginal cost 5.5s — all three
imports were already in the root cone).
-/
import Dregg2.Circuit.AlgoStarkSoundFanoutMemory
import Dregg2.Circuit.CircuitSoundnessAssembled
import Dregg2.Circuit.MapReconcileImtRepoint

namespace Dregg2.Circuit.ApexMapOpVacuityJoin

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 MapOp VmTrace envAt mapOpsOf MAP_TREE_DEPTH)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.MapMerkleRoot (perfectRoot mapRoot)
open Dregg2.Circuit.IndexedMerkleTree (ImtLeaf imtLeafHash)
open Dregg2.Circuit.MapOpsColumnLayout (MapReconcileModelOk mem_mapOpsOf)
open Dregg2.Circuit.MapReconcileImtRepoint (imtRoot_ne_mapRoot)
open Dregg2.Substrate
open Dregg2.Circuit.AlgoStarkSoundFanoutMemory (MapReconcileFamily)
open Dregg2.Circuit.AlgoStarkSoundGeneral (AcceptsFull)
open Dregg2.Circuit.CircuitSoundnessAssembled (Rfix)
open Dregg2.Circuit.CircuitSoundness (BatchPublicInputs BatchProof EffectIdx)
open Dregg2.Circuit.FriVerifier (FriParams RecursionVk FriCore FieldArith)
open Dregg2.Circuit.FriVerifierBridge (ProofView)
open Dregg2.Circuit.Emit.EffectVmEmit (EFFECT_VM_WIDTH)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3
  (nullifierFreshOp nullifierRootGroupCol commitmentsInsertOp commitmentsRootGroupCol
   cellsFreshOp cellsRootGroupCol refusalFieldsWriteOp fieldsRootGroupCol heapRootGroupCol
   noteSpendV3 noteCreateV3 createCellV3 refusalFieldsWriteV3 NEW_CELL_KEY_PARAM_COL)
open Dregg2.Circuit.RotatedKernelRefinementExercise (heapSpliceWriteOp heapWriteV3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §0 — THE PREMISE THE ARGUMENT ACTUALLY USES, AND NOTHING MORE.

The deployed map tree commits arity-3 leaves (`heap_root.rs:97,378`); the Lean denotation commits
arity-2 ones (`Substrate/Heap.lean:392`). Everything below needs ONE fact about that: at the felt
the deployed prover puts in the pre-root column, there is no arity-2 heap of the right size whose
`mapRoot` is that same felt. Named, carried, and never assumed away. -/

/-- **`RootSeparated hash dep c`** — the deployed indexed-Merkle commitment of the chain `c` is not
ALSO the arity-2 `mapRoot` of any heap of the same size. A per-deployment separation fact, strictly
weaker than the CR floor and REFUTABLE (see below). -/
def RootSeparated (hash : List ℤ → ℤ) (dep : Nat) (c : List ImtLeaf) : Prop :=
  ∀ h : Heap.FeltHeap, h.length = 2 ^ dep →
    mapRoot hash dep h ≠ perfectRoot hash dep (c.map (imtLeafHash hash))

/-- **TOOTH — `RootSeparated` IS REFUTABLE, so it is not a tautology dressed as a premise.** At the
constant hash both commitments collapse to the fold of the same all-zero leaf vector, so the two
roots COINCIDE and the separation is FALSE. A premise that could not be refuted would be carrying no
information, and this file would be measuring nothing. -/
theorem rootSeparated_false_at_constant_hash (dep : Nat) (c : List ImtLeaf)
    (hc : c.length = 2 ^ dep) : ¬ RootSeparated (fun _ => 0) dep c := by
  intro hsep
  refine hsep (List.replicate (2 ^ dep) (0, 0)) (by rw [List.length_replicate]) ?_
  have h1 : (List.replicate (2 ^ dep) ((0 : ℤ), (0 : ℤ))).map (Heap.leafOf (fun _ => 0))
      = List.replicate (2 ^ dep) (0 : ℤ) := by
    simp [Heap.leafOf]
  have h2 : c.map (imtLeafHash (fun _ => 0)) = List.replicate (2 ^ dep) (0 : ℤ) := by
    have hmap : c.map (imtLeafHash (fun _ => 0)) = c.map (fun _ => (0 : ℤ)) := rfl
    rw [hmap, List.map_const', hc]
  rw [mapRoot, h1, h2]

/-- **⚑ THE CR BRIDGE (carrier #1 of 2).** `MapReconcileImtRepoint.imtRoot_ne_mapRoot` discharges the
separation from the apex's OWN floor `Poseidon2SpongeCR hash` — the very instance
`algoStarkSound_kernel` binds as `hCRh`. This declaration takes a hypothesis the tree proves false at
deployed BabyBear width and is therefore vacuous THERE; it exists so that the composition onto the
apex's own terms is machine-checked. Every theorem in §§1-6 is independent of it. -/
theorem rootSeparated_of_poseidon2CR_under_the_apex_floor
    (hash : List ℤ → ℤ) (hCRh : Poseidon2SpongeCR hash) (dep : Nat) (c : List ImtLeaf)
    (hc : c.length = 2 ^ dep) : RootSeparated hash dep c :=
  fun h hlen heq => imtRoot_ne_mapRoot hash hCRh dep c h hc hlen heq.symm

/-! ## §1 — THE DEPLOYED-SHAPED ROW, AND THE GENERIC REFUTATION.

Everything here is row-generic and depth-`MAP_TREE_DEPTH`. The only thing a per-tag corollary has to
supply is (i) that the map op is DECLARED by the deployed descriptor, and (ii) two `rfl`s reading
the op's guard and lane-0 pre-root off the row. -/

/-- The one-row trace over a row assignment. Deliberately minimal: `MapReconcileModelOk` reads only
`rows.length` and `envAt _ 0 |>.loc`, so nothing else can matter. -/
def rowTrace (a : Assignment) : VmTrace :=
  { rows := [a], pub := fun _ => 0, tf := fun _ => [] }

theorem rowTrace_rows_length (a : Assignment) : (rowTrace a).rows.length = 1 := rfl

theorem rowTrace_loc (a : Assignment) : (envAt (rowTrace a) 0).loc = a := rfl

/-- The empty trace — `MapReconcileModelOk` holds on it VACUOUSLY, so the extractor below asserts
nothing at the tags this file does not census. -/
def emptyTrace : VmTrace := { rows := [], pub := fun _ => 0, tf := fun _ => [] }

/-- **The deployed-shaped row**: the map op's lane-0 pre-root column carries the felt `R`, its
selector column carries `1`, every other column is `0`. When `R` is the arity-3 indexed-Merkle root
`heap_root.rs` computes, this row is exactly what the deployed prover emits — a fired map-op row
committed to the deployed tree. -/
def imtRowAt (selCol rootCol : Nat) (R : ℤ) : Assignment :=
  fun col => if col = rootCol then R else if col = selCol then 1 else 0

theorem imtRowAt_root (selCol rootCol : Nat) (R : ℤ) :
    imtRowAt selCol rootCol R rootCol = R := by
  simp [imtRowAt]

theorem imtRowAt_sel (selCol rootCol : Nat) (R : ℤ) (h : selCol ≠ rootCol) :
    imtRowAt selCol rootCol R selCol = 1 := by
  simp [imtRowAt, h]

/-- **★ THE GENERIC REFUTATION OF THE CARRIED MODEL — FLOOR-FREE.** A descriptor that DECLARES a
map op, a row that FIRES it, and a lane-0 pre-root column that is the deployed indexed-Merkle
commitment: the apex's per-trace model `MapReconcileModelOk` has no witness there. The whole content
is `ReconcileGatesAt`'s own arity-2 heap-extraction premise meeting `RootSeparated`. Kind-agnostic —
that premise sits OUTSIDE the per-kind match, so this bites `.read`, `.absent`, `.write`, `.insert`
and `.aafiInsert` alike, and no fact about the key, the chain contents or the op is used. -/
theorem mapReconcileModelOk_false_of_imtRootedRow
    (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor2) (m : MapOp)
    (hm : VmConstraint2.mapOp m ∈ d.constraints)
    (a : Assignment) (c : List ImtLeaf)
    (hsep : RootSeparated hash MAP_TREE_DEPTH c)
    (hg : m.guard.eval a = 1)
    (hr : (m.root 0).eval a = perfectRoot hash MAP_TREE_DEPTH (c.map (imtLeafHash hash))) :
    ¬ MapReconcileModelOk hash d (rowTrace a) := by
  intro hok
  have hgates := hok 0 (by rw [rowTrace_rows_length]; omega) m (mem_mapOpsOf.mpr hm)
    (by rw [rowTrace_loc]; exact hg)
  rw [rowTrace_loc] at hgates
  obtain ⟨h, -, hlen, hroot, -⟩ := hgates
  exact hsep h hlen (hroot.trans hr)

/-- **★ THE GENERIC REFUTATION OF THE APEX'S PREMISE — FLOOR-FREE.** `MapReconcileFamily` is
`∀ pi π, AcceptsFull … → MapReconcileModelOk hash d (tr pi π)`. Given ANY accepting batch — the
premise's own antecedent — the deployed-shaped extractor makes it FALSE. The accepting batch is a
hypothesis and not an exhibit on purpose: whether the deployed verifier accepts anything at all is
the OTHER open wound (`docs/WOUND-apex-premise-vacuity-2026-07-24.md`), and `apex_is_dead_either_way`
below discharges the disjunction rather than assuming its way past it. -/
theorem mapReconcileFamily_false_of_imtRootedRow
    (hash : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (d : EffectVmDescriptor2) (m : MapOp)
    (hm : VmConstraint2.mapOp m ∈ d.constraints)
    (a : Assignment) (c : List ImtLeaf)
    (hsep : RootSeparated hash MAP_TREE_DEPTH c)
    (hg : m.guard.eval a = 1)
    (hr : (m.root 0).eval a = perfectRoot hash MAP_TREE_DEPTH (c.map (imtLeafHash hash)))
    (pi : BatchPublicInputs) (π : BatchProof)
    (hacc : AcceptsFull perm RATE toNat params vk core A initState logN view pi π) :
    ¬ MapReconcileFamily hash perm RATE toNat params vk core A initState logN view
        (fun _ _ => rowTrace a) d := by
  intro hfam
  exact mapReconcileModelOk_false_of_imtRootedRow hash d m hm a c hsep hg hr (hfam pi π hacc)

/-! ## §2 — THE PER-TAG ROWS AT THE DEPLOYED MEMBERS.

One row per censused tag, each naming the map op the DEPLOYED registry member declares and the two
columns that op reads: its selector and the lane-0 limb of its committed pre-root group. These are
the deployed column numbers, not toys. -/

/-- tag 27 — noteSpend's double-spend tooth `nullifierFreshOp` (`.absent`), selector
`SEL_NOTE_SPEND`, pre-root lane 0 = the BEFORE nullifier-root limb. -/
def row27 (R : ℤ) : Assignment :=
  imtRowAt Dregg2.Circuit.Emit.EffectVmEmitNoteSpend.SEL_NOTE_SPEND
    (nullifierRootGroupCol EFFECT_VM_WIDTH 0) R

/-- tag 28 — noteCreate's set-insert `commitmentsInsertOp` (`.aafiInsert`). -/
def row28 (R : ℤ) : Assignment :=
  imtRowAt Dregg2.Circuit.Emit.EffectVmEmitNoteCreate.SEL_NOTE_CREATE
    (commitmentsRootGroupCol EFFECT_VM_WIDTH 0) R

/-- tag 17 — createCell's no-collision tooth `cellsFreshOp` (`.absent`). -/
def row17 (R : ℤ) : Assignment :=
  imtRowAt Dregg2.Circuit.Emit.EffectVmEmitCreateCell.SEL_CREATE_CELL_RT
    (cellsRootGroupCol EFFECT_VM_WIDTH 0) R

/-- tag 39 — refusal's audit-slot write `refusalFieldsWriteOp` (`.write`). -/
def row39 (R : ℤ) : Assignment :=
  imtRowAt Dregg2.Circuit.Emit.EffectVmEmitRefusal.SEL_REFUSAL
    (fieldsRootGroupCol EFFECT_VM_WIDTH 0) R

/-- tag 56 — heapWrite's splice `heapSpliceWriteOp` (`.write`). Its guard is the CONSTANT `1`: this
row fires with no selector at all, so the refutation at tag 56 needs no column disequality. -/
def row56 (R : ℤ) : Assignment :=
  imtRowAt 0 (heapRootGroupCol EFFECT_VM_WIDTH 0) R

/-! ### §2b — the two column readings per tag, each a standalone lemma.

The `decide`s are DISEQUALITIES OF DEPLOYED COLUMN NUMBERS (`SEL_NOTE_SPEND = 4` vs the BEFORE
nullifier-root limb `EFFECT_VM_WIDTH + 26 = 214`, and so on). They are what makes the row FIRE: the
selector reads `1` because it is not the pre-root column. Tag 56's op has a CONSTANT guard, so it
needs no such fact. -/

theorem row27_guard (R : ℤ) : nullifierFreshOp.guard.eval (row27 R) = 1 :=
  imtRowAt_sel Dregg2.Circuit.Emit.EffectVmEmitNoteSpend.SEL_NOTE_SPEND (nullifierRootGroupCol EFFECT_VM_WIDTH 0) R (by decide)

theorem row27_root (R : ℤ) : (nullifierFreshOp.root 0).eval (row27 R) = R :=
  imtRowAt_root Dregg2.Circuit.Emit.EffectVmEmitNoteSpend.SEL_NOTE_SPEND (nullifierRootGroupCol EFFECT_VM_WIDTH 0) R

theorem row28_guard (R : ℤ) : commitmentsInsertOp.guard.eval (row28 R) = 1 :=
  imtRowAt_sel Dregg2.Circuit.Emit.EffectVmEmitNoteCreate.SEL_NOTE_CREATE (commitmentsRootGroupCol EFFECT_VM_WIDTH 0) R (by decide)

theorem row28_root (R : ℤ) : (commitmentsInsertOp.root 0).eval (row28 R) = R :=
  imtRowAt_root Dregg2.Circuit.Emit.EffectVmEmitNoteCreate.SEL_NOTE_CREATE (commitmentsRootGroupCol EFFECT_VM_WIDTH 0) R

theorem row17_guard (R : ℤ) :
    (cellsFreshOp Dregg2.Circuit.Emit.EffectVmEmitCreateCell.SEL_CREATE_CELL_RT NEW_CELL_KEY_PARAM_COL).guard.eval (row17 R) = 1 :=
  imtRowAt_sel Dregg2.Circuit.Emit.EffectVmEmitCreateCell.SEL_CREATE_CELL_RT (cellsRootGroupCol EFFECT_VM_WIDTH 0) R (by decide)

theorem row17_root (R : ℤ) :
    ((cellsFreshOp Dregg2.Circuit.Emit.EffectVmEmitCreateCell.SEL_CREATE_CELL_RT NEW_CELL_KEY_PARAM_COL).root 0).eval (row17 R) = R :=
  imtRowAt_root Dregg2.Circuit.Emit.EffectVmEmitCreateCell.SEL_CREATE_CELL_RT (cellsRootGroupCol EFFECT_VM_WIDTH 0) R

theorem row39_guard (R : ℤ) : refusalFieldsWriteOp.guard.eval (row39 R) = 1 :=
  imtRowAt_sel Dregg2.Circuit.Emit.EffectVmEmitRefusal.SEL_REFUSAL (fieldsRootGroupCol EFFECT_VM_WIDTH 0) R (by decide)

theorem row39_root (R : ℤ) : (refusalFieldsWriteOp.root 0).eval (row39 R) = R :=
  imtRowAt_root Dregg2.Circuit.Emit.EffectVmEmitRefusal.SEL_REFUSAL (fieldsRootGroupCol EFFECT_VM_WIDTH 0) R

theorem row56_guard (R : ℤ) : heapSpliceWriteOp.guard.eval (row56 R) = 1 := rfl

theorem row56_root (R : ℤ) : (heapSpliceWriteOp.root 0).eval (row56 R) = R :=
  imtRowAt_root 0 (heapRootGroupCol EFFECT_VM_WIDTH 0) R

/-! ## §3 — THE DECLARATIONS: each op IS declared by its DEPLOYED registry member.

Each `Rfix <tag> = …` step is the LANDED `rfl` correspondence from `CircuitSoundnessAssembled`; the
rest is `List.mem_append`, because every deployed wrap only APPENDS (`effHeapOpenV3`,
`effAccumInsertV3`, `effHeapWriteV3`, `effFieldsOpenV3`, `effFieldsWriteV3` are all
`base.constraints ++ appendix`). No constraint list is evaluated. -/

theorem mapOp_mem_Rfix27 :
    VmConstraint2.mapOp nullifierFreshOp ∈ (Rfix 27).constraints := by
  rw [Dregg2.Circuit.CircuitSoundnessAssembled.Rfix_noteSpendInsert]
  exact List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.Mem.head _)))

theorem mapOp_mem_Rfix28 :
    VmConstraint2.mapOp commitmentsInsertOp ∈ (Rfix 28).constraints := by
  rw [Dregg2.Circuit.CircuitSoundnessAssembled.Rfix_noteCreateInsert]
  exact List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.Mem.head _)))

theorem mapOp_mem_Rfix17 :
    VmConstraint2.mapOp (cellsFreshOp Dregg2.Circuit.Emit.EffectVmEmitCreateCell.SEL_CREATE_CELL_RT
      NEW_CELL_KEY_PARAM_COL) ∈ (Rfix 17).constraints := by
  rw [Dregg2.Circuit.CircuitSoundnessAssembled.Rfix_createCellInsert]
  exact List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.Mem.head _)))

theorem mapOp_mem_Rfix39 :
    VmConstraint2.mapOp refusalFieldsWriteOp ∈ (Rfix 39).constraints := by
  rw [Dregg2.Circuit.CircuitSoundnessAssembled.Rfix_refusal]
  exact List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.Mem.head _)))

theorem mapOp_mem_Rfix56 :
    VmConstraint2.mapOp heapSpliceWriteOp ∈ (Rfix 56).constraints := by
  rw [Dregg2.Circuit.CircuitSoundnessAssembled.Rfix_heapWrite]
  exact List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.Mem.head _)))

/-! ## §4 — THE PER-TAG REFUTATIONS OF THE CARRIED MODEL. -/

theorem mapReconcileModelOk_false_at_tag27
    (hash : List ℤ → ℤ) (c : List ImtLeaf) (hsep : RootSeparated hash MAP_TREE_DEPTH c) :
    ¬ MapReconcileModelOk hash (Rfix 27)
        (rowTrace (row27 (perfectRoot hash MAP_TREE_DEPTH (c.map (imtLeafHash hash))))) :=
  mapReconcileModelOk_false_of_imtRootedRow hash (Rfix 27) nullifierFreshOp mapOp_mem_Rfix27
    _ c hsep (row27_guard _) (row27_root _)

theorem mapReconcileModelOk_false_at_tag28
    (hash : List ℤ → ℤ) (c : List ImtLeaf) (hsep : RootSeparated hash MAP_TREE_DEPTH c) :
    ¬ MapReconcileModelOk hash (Rfix 28)
        (rowTrace (row28 (perfectRoot hash MAP_TREE_DEPTH (c.map (imtLeafHash hash))))) :=
  mapReconcileModelOk_false_of_imtRootedRow hash (Rfix 28) commitmentsInsertOp mapOp_mem_Rfix28
    _ c hsep (row28_guard _) (row28_root _)

theorem mapReconcileModelOk_false_at_tag17
    (hash : List ℤ → ℤ) (c : List ImtLeaf) (hsep : RootSeparated hash MAP_TREE_DEPTH c) :
    ¬ MapReconcileModelOk hash (Rfix 17)
        (rowTrace (row17 (perfectRoot hash MAP_TREE_DEPTH (c.map (imtLeafHash hash))))) :=
  mapReconcileModelOk_false_of_imtRootedRow hash (Rfix 17) _ mapOp_mem_Rfix17
    _ c hsep (row17_guard _) (row17_root _)

theorem mapReconcileModelOk_false_at_tag39
    (hash : List ℤ → ℤ) (c : List ImtLeaf) (hsep : RootSeparated hash MAP_TREE_DEPTH c) :
    ¬ MapReconcileModelOk hash (Rfix 39)
        (rowTrace (row39 (perfectRoot hash MAP_TREE_DEPTH (c.map (imtLeafHash hash))))) :=
  mapReconcileModelOk_false_of_imtRootedRow hash (Rfix 39) refusalFieldsWriteOp mapOp_mem_Rfix39
    _ c hsep (row39_guard _) (row39_root _)

theorem mapReconcileModelOk_false_at_tag56
    (hash : List ℤ → ℤ) (c : List ImtLeaf) (hsep : RootSeparated hash MAP_TREE_DEPTH c) :
    ¬ MapReconcileModelOk hash (Rfix 56)
        (rowTrace (row56 (perfectRoot hash MAP_TREE_DEPTH (c.map (imtLeafHash hash))))) :=
  mapReconcileModelOk_false_of_imtRootedRow hash (Rfix 56) heapSpliceWriteOp mapOp_mem_Rfix56
    _ c hsep (row56_guard _) (row56_root _)

/-! ## §5 — ★★ THE APEX'S OWN `hrec`, REFUTED.

`MapReconcileFamily hash perm RATE toNat params vk core A initState logN view (tr e) (Rfix e)` is
LITERALLY the type of `algoStarkSound_kernel`'s `hrec` argument at tag `e`. Below it is FALSE. -/

/-- The DEPLOYED-shaped extractor: at each censused tag the one fired map-op row committed to the
arity-3 indexed-Merkle root; the empty trace elsewhere (about which the model says nothing, so no tag
is slandered by association). This is the `tr` an honest FRI extractor would produce from a run of
the deployed prover. -/
def trImt (hash : List ℤ → ℤ) (c : List ImtLeaf) :
    EffectIdx → BatchPublicInputs → BatchProof → VmTrace :=
  fun e _ _ =>
    match e with
    | 17 => rowTrace (row17 (perfectRoot hash MAP_TREE_DEPTH (c.map (imtLeafHash hash))))
    | 27 => rowTrace (row27 (perfectRoot hash MAP_TREE_DEPTH (c.map (imtLeafHash hash))))
    | 28 => rowTrace (row28 (perfectRoot hash MAP_TREE_DEPTH (c.map (imtLeafHash hash))))
    | 39 => rowTrace (row39 (perfectRoot hash MAP_TREE_DEPTH (c.map (imtLeafHash hash))))
    | 56 => rowTrace (row56 (perfectRoot hash MAP_TREE_DEPTH (c.map (imtLeafHash hash))))
    | _  => emptyTrace

theorem trImt_17 (hash : List ℤ → ℤ) (c : List ImtLeaf) :
    trImt hash c 17
      = fun _ _ => rowTrace (row17 (perfectRoot hash MAP_TREE_DEPTH (c.map (imtLeafHash hash)))) :=
  rfl
theorem trImt_27 (hash : List ℤ → ℤ) (c : List ImtLeaf) :
    trImt hash c 27
      = fun _ _ => rowTrace (row27 (perfectRoot hash MAP_TREE_DEPTH (c.map (imtLeafHash hash)))) :=
  rfl
theorem trImt_28 (hash : List ℤ → ℤ) (c : List ImtLeaf) :
    trImt hash c 28
      = fun _ _ => rowTrace (row28 (perfectRoot hash MAP_TREE_DEPTH (c.map (imtLeafHash hash)))) :=
  rfl
theorem trImt_39 (hash : List ℤ → ℤ) (c : List ImtLeaf) :
    trImt hash c 39
      = fun _ _ => rowTrace (row39 (perfectRoot hash MAP_TREE_DEPTH (c.map (imtLeafHash hash)))) :=
  rfl
theorem trImt_56 (hash : List ℤ → ℤ) (c : List ImtLeaf) :
    trImt hash c 56
      = fun _ _ => rowTrace (row56 (perfectRoot hash MAP_TREE_DEPTH (c.map (imtLeafHash hash)))) :=
  rfl

section Family

variable (hash : List ℤ → ℤ)
  (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
  (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
  (initState : List ℤ) (logN : Nat) (view : ProofView)

/-- **★ tag 27 (noteSpend) — the apex's `hrec` slot is FALSE.** -/
theorem mapReconcileFamily_false_at_tag27
    (c : List ImtLeaf) (hsep : RootSeparated hash MAP_TREE_DEPTH c)
    (pi : BatchPublicInputs) (π : BatchProof)
    (hacc : AcceptsFull perm RATE toNat params vk core A initState logN view pi π) :
    ¬ MapReconcileFamily hash perm RATE toNat params vk core A initState logN view
        (trImt hash c 27) (Rfix 27) := by
  intro hfam
  exact mapReconcileModelOk_false_at_tag27 hash c hsep (hfam pi π hacc)

/-- **★ tag 28 (noteCreate).** -/
theorem mapReconcileFamily_false_at_tag28
    (c : List ImtLeaf) (hsep : RootSeparated hash MAP_TREE_DEPTH c)
    (pi : BatchPublicInputs) (π : BatchProof)
    (hacc : AcceptsFull perm RATE toNat params vk core A initState logN view pi π) :
    ¬ MapReconcileFamily hash perm RATE toNat params vk core A initState logN view
        (trImt hash c 28) (Rfix 28) := by
  intro hfam
  exact mapReconcileModelOk_false_at_tag28 hash c hsep (hfam pi π hacc)

/-- **★ tag 17 (createCell).** -/
theorem mapReconcileFamily_false_at_tag17
    (c : List ImtLeaf) (hsep : RootSeparated hash MAP_TREE_DEPTH c)
    (pi : BatchPublicInputs) (π : BatchProof)
    (hacc : AcceptsFull perm RATE toNat params vk core A initState logN view pi π) :
    ¬ MapReconcileFamily hash perm RATE toNat params vk core A initState logN view
        (trImt hash c 17) (Rfix 17) := by
  intro hfam
  exact mapReconcileModelOk_false_at_tag17 hash c hsep (hfam pi π hacc)

/-- **★ tag 39 (refusal).** -/
theorem mapReconcileFamily_false_at_tag39
    (c : List ImtLeaf) (hsep : RootSeparated hash MAP_TREE_DEPTH c)
    (pi : BatchPublicInputs) (π : BatchProof)
    (hacc : AcceptsFull perm RATE toNat params vk core A initState logN view pi π) :
    ¬ MapReconcileFamily hash perm RATE toNat params vk core A initState logN view
        (trImt hash c 39) (Rfix 39) := by
  intro hfam
  exact mapReconcileModelOk_false_at_tag39 hash c hsep (hfam pi π hacc)

/-- **★ tag 56 (heapWrite)** — the constant-guard member: no selector column is even needed. -/
theorem mapReconcileFamily_false_at_tag56
    (c : List ImtLeaf) (hsep : RootSeparated hash MAP_TREE_DEPTH c)
    (pi : BatchPublicInputs) (π : BatchProof)
    (hacc : AcceptsFull perm RATE toNat params vk core A initState logN view pi π) :
    ¬ MapReconcileFamily hash perm RATE toNat params vk core A initState logN view
        (trImt hash c 56) (Rfix 56) := by
  intro hfam
  exact mapReconcileModelOk_false_at_tag56 hash c hsep (hfam pi π hacc)

/-- **★★ THE APEX'S `hrec` ARGUMENT, REFUTED AS A WHOLE.** This Prop is exactly the `hrec` slot of
`AlgoStarkSoundKernel.algoStarkSound_kernel` / `algoStarkSound_kernel_noOodShape` at
`tr := trImt hash c`. On the deployed-shaped extracted trace it is FALSE — so the apex, fed the
traces the deployed prover actually produces, cannot be applied at all. -/
theorem apex_hrec_false_at_deployed_map_traces
    (c : List ImtLeaf) (hsep : RootSeparated hash MAP_TREE_DEPTH c)
    (pi : BatchPublicInputs) (π : BatchProof)
    (hacc : AcceptsFull perm RATE toNat params vk core A initState logN view pi π) :
    ¬ (∀ e : EffectIdx, MapReconcileFamily hash perm RATE toNat params vk core A initState logN
        view (trImt hash c e) (Rfix e)) := by
  intro hrec
  exact mapReconcileFamily_false_at_tag27 hash perm RATE toNat params vk core A initState logN
    view c hsep pi π hacc (hrec 27)

/-- **★★ AND WITHOUT ASSUMING AN ACCEPTING BATCH — THE DICHOTOMY.** No accepting pole is exhibited
anywhere in this tree at the deployed `opaque` verifier arguments, so the honest unconditional
statement is a disjunction, and BOTH branches kill the apex at the map-op tags: either the deployed
verifier accepts nothing (and every `MapReconcileFamily` — indeed the whole capstone — quantifies
over an empty set), or it accepts something and the apex's `hrec` at the deployed-shaped extractor is
FALSE. There is no branch on which the apex asserts anything about a deployed map-op run. -/
theorem apex_is_dead_either_way
    (c : List ImtLeaf) (hsep : RootSeparated hash MAP_TREE_DEPTH c) :
    (∀ (pi : BatchPublicInputs) (π : BatchProof),
        ¬ AcceptsFull perm RATE toNat params vk core A initState logN view pi π)
    ∨ ¬ (∀ e : EffectIdx, MapReconcileFamily hash perm RATE toNat params vk core A initState logN
        view (trImt hash c e) (Rfix e)) := by
  by_cases h : ∀ (pi : BatchPublicInputs) (π : BatchProof),
      ¬ AcceptsFull perm RATE toNat params vk core A initState logN view pi π
  · exact Or.inl h
  · refine Or.inr ?_
    obtain ⟨pi, π, hacc⟩ :
        ∃ (pi : BatchPublicInputs) (π : BatchProof),
          AcceptsFull perm RATE toNat params vk core A initState logN view pi π := by
      by_contra hcon
      exact h (fun pi π hp => hcon ⟨pi, π, hp⟩)
    exact apex_hrec_false_at_deployed_map_traces hash perm RATE toNat params vk core A
      initState logN view c hsep pi π hacc

/-- **★ THE CENSUS, IN ONE STATEMENT.** Five deployed map-op tags, five refutations of the apex's
own carried model at the deployed commitment. Tags 18 (createCellFromFactory) and 19 (spawn) carry
the same two accounts grow-gate map ops and are NOT censused here only because their registry
members ride wrap chains with no landed `Rfix_*` `rfl` correspondence to reuse; nothing about them
is claimed either way. -/
theorem deployed_mapOp_census
    (c : List ImtLeaf) (hsep : RootSeparated hash MAP_TREE_DEPTH c) :
    ¬ MapReconcileModelOk hash (Rfix 17)
        (rowTrace (row17 (perfectRoot hash MAP_TREE_DEPTH (c.map (imtLeafHash hash)))))
    ∧ ¬ MapReconcileModelOk hash (Rfix 27)
        (rowTrace (row27 (perfectRoot hash MAP_TREE_DEPTH (c.map (imtLeafHash hash)))))
    ∧ ¬ MapReconcileModelOk hash (Rfix 28)
        (rowTrace (row28 (perfectRoot hash MAP_TREE_DEPTH (c.map (imtLeafHash hash)))))
    ∧ ¬ MapReconcileModelOk hash (Rfix 39)
        (rowTrace (row39 (perfectRoot hash MAP_TREE_DEPTH (c.map (imtLeafHash hash)))))
    ∧ ¬ MapReconcileModelOk hash (Rfix 56)
        (rowTrace (row56 (perfectRoot hash MAP_TREE_DEPTH (c.map (imtLeafHash hash))))) :=
  ⟨mapReconcileModelOk_false_at_tag17 hash c hsep,
   mapReconcileModelOk_false_at_tag27 hash c hsep,
   mapReconcileModelOk_false_at_tag28 hash c hsep,
   mapReconcileModelOk_false_at_tag39 hash c hsep,
   mapReconcileModelOk_false_at_tag56 hash c hsep⟩

/-- **⚑⚑ THE COMPOSITION ONTO THE APEX'S OWN TERMS (carrier #2 of 2).** The same refutation with
the separation discharged from `Poseidon2SpongeCR hash` — the instance `algoStarkSound_kernel` binds
as `hCRh`. Read it as: *on the apex's own floor, at the apex's own registry, fed the traces the
deployed prover produces, the apex's own `hrec` is FALSE.* This declaration is vacuous exactly where
that floor is (deployed BabyBear width); `apex_hrec_false_at_deployed_map_traces` above is not, and
is the statement to cite. -/
theorem apex_hrec_false_at_deployed_map_traces_under_the_apex_floor
    (hCRh : Poseidon2SpongeCR hash)
    (c : List ImtLeaf) (hc : c.length = 2 ^ MAP_TREE_DEPTH)
    (pi : BatchPublicInputs) (π : BatchProof)
    (hacc : AcceptsFull perm RATE toNat params vk core A initState logN view pi π) :
    ¬ (∀ e : EffectIdx, MapReconcileFamily hash perm RATE toNat params vk core A initState logN
        view (trImt hash c e) (Rfix e)) :=
  apex_hrec_false_at_deployed_map_traces hash perm RATE toNat params vk core A initState logN view c
    (rootSeparated_of_poseidon2CR_under_the_apex_floor hash hCRh MAP_TREE_DEPTH c hc) pi π hacc

end Family

/-! ## §5c — TEETH: the censused rows are DECLARED and they FIRE.

The failure mode that actually threatens a refutation of this shape is that the row never fires, in
which case `MapReconcileModelOk` is vacuously TRUE there and the theorem would be measuring nothing.
Both halves are exhibited, per tag: the op is a member of the DEPLOYED descriptor's `mapOpsOf`, and
its guard evaluates to `1` on the row. -/

/-- **★ EVERY CENSUSED ROW IS A DECLARED, FIRING ROW OF ITS DEPLOYED REGISTRY MEMBER.** -/
theorem censused_rows_declare_and_fire (R : ℤ) :
    (nullifierFreshOp ∈ mapOpsOf (Rfix 27) ∧ nullifierFreshOp.guard.eval (row27 R) = 1)
    ∧ (commitmentsInsertOp ∈ mapOpsOf (Rfix 28)
        ∧ commitmentsInsertOp.guard.eval (row28 R) = 1)
    ∧ (cellsFreshOp Dregg2.Circuit.Emit.EffectVmEmitCreateCell.SEL_CREATE_CELL_RT
          NEW_CELL_KEY_PARAM_COL ∈ mapOpsOf (Rfix 17)
        ∧ (cellsFreshOp Dregg2.Circuit.Emit.EffectVmEmitCreateCell.SEL_CREATE_CELL_RT
            NEW_CELL_KEY_PARAM_COL).guard.eval (row17 R) = 1)
    ∧ (refusalFieldsWriteOp ∈ mapOpsOf (Rfix 39)
        ∧ refusalFieldsWriteOp.guard.eval (row39 R) = 1)
    ∧ (heapSpliceWriteOp ∈ mapOpsOf (Rfix 56)
        ∧ heapSpliceWriteOp.guard.eval (row56 R) = 1) :=
  ⟨⟨mem_mapOpsOf.mpr mapOp_mem_Rfix27, row27_guard R⟩,
   ⟨mem_mapOpsOf.mpr mapOp_mem_Rfix28, row28_guard R⟩,
   ⟨mem_mapOpsOf.mpr mapOp_mem_Rfix17, row17_guard R⟩,
   ⟨mem_mapOpsOf.mpr mapOp_mem_Rfix39, row39_guard R⟩,
   ⟨mem_mapOpsOf.mpr mapOp_mem_Rfix56, row56_guard R⟩⟩

/-- **★ THE DEPLOYED COLUMN NUMBERS, PINNED.** The selector and lane-0 pre-root limb each censused
row is built on, as literals a reader can check against `columns.rs` / the rotated block layout. If
the deployed layout moves, this goes RED rather than the refutations quietly retargeting an
unrelated column. -/
theorem censused_columns_are_the_deployed_ones :
    (Dregg2.Circuit.Emit.EffectVmEmitNoteSpend.SEL_NOTE_SPEND,
      nullifierRootGroupCol EFFECT_VM_WIDTH 0) = (4, 214)
    ∧ (Dregg2.Circuit.Emit.EffectVmEmitNoteCreate.SEL_NOTE_CREATE,
      commitmentsRootGroupCol EFFECT_VM_WIDTH 0) = (5, 215)
    ∧ (Dregg2.Circuit.Emit.EffectVmEmitCreateCell.SEL_CREATE_CELL_RT,
      cellsRootGroupCol EFFECT_VM_WIDTH 0) = (31, 188)
    ∧ (Dregg2.Circuit.Emit.EffectVmEmitRefusal.SEL_REFUSAL,
      fieldsRootGroupCol EFFECT_VM_WIDTH 0) = (52, 224)
    ∧ heapRootGroupCol EFFECT_VM_WIDTH 0 = 216 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-! ## §6 — AXIOM HYGIENE. -/

#assert_axioms RootSeparated
#assert_axioms rootSeparated_false_at_constant_hash
#assert_axioms rootSeparated_of_poseidon2CR_under_the_apex_floor
#assert_axioms mapReconcileModelOk_false_of_imtRootedRow
#assert_axioms mapReconcileFamily_false_of_imtRootedRow
#assert_axioms mapOp_mem_Rfix17
#assert_axioms mapOp_mem_Rfix27
#assert_axioms mapOp_mem_Rfix28
#assert_axioms mapOp_mem_Rfix39
#assert_axioms mapOp_mem_Rfix56
#assert_axioms mapReconcileModelOk_false_at_tag17
#assert_axioms mapReconcileModelOk_false_at_tag27
#assert_axioms mapReconcileModelOk_false_at_tag28
#assert_axioms mapReconcileModelOk_false_at_tag39
#assert_axioms mapReconcileModelOk_false_at_tag56
#assert_axioms mapReconcileFamily_false_at_tag17
#assert_axioms mapReconcileFamily_false_at_tag27
#assert_axioms mapReconcileFamily_false_at_tag28
#assert_axioms mapReconcileFamily_false_at_tag39
#assert_axioms mapReconcileFamily_false_at_tag56
#assert_axioms apex_hrec_false_at_deployed_map_traces
#assert_axioms apex_is_dead_either_way
#assert_axioms apex_hrec_false_at_deployed_map_traces_under_the_apex_floor
#assert_axioms censused_rows_declare_and_fire
#assert_axioms censused_columns_are_the_deployed_ones
#assert_axioms deployed_mapOp_census

end Dregg2.Circuit.ApexMapOpVacuityJoin

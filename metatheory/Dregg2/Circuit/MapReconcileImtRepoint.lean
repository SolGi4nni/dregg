/-
# `Dregg2.Circuit.MapReconcileImtRepoint` — the `.absent` dispatch REPOINTED onto the deployed
  shape, and the WALL that repointing runs into one layer above.

## The two findings, first (both machine-checked below)

1. **The repointed model exists and is INHABITED on the ordinary path.** `ReconcileGatesImtAt`
   dispatches the `.absent` arm to `MapAbsentImtGate.AbsentImtGatesAt` — the deployed
   `Ir2Air::MapAbsent` shape (ONE arity-3 low-leaf opening with the pointer INSIDE the digest, the
   pointer bracket, `new_root = root`) — carrying the committed chain in the SAME `∃ h` slot
   `ReconcileGatesAt` already uses. §4 exhibits a row AT THE DEPLOYED DEPTH `MAP_TREE_DEPTH = 16`
   where the OLD per-row body is FALSE and the repointed one HOLDS, and the repointed law fires the
   absence. No `2^16`-element object is ever evaluated: the witness spine is built by a cons
   recursion and split by `spineC_add` exactly where `perfectRoot_append` splits the tree.

2. **⚠ THE APEX CANNOT BE DE-VACUUMED BY REPOINTING THE PREMISE.** The apex consumes
   `MapReconcileModelOk` through `mapOpsArm_of_modeler → MapOp.holdsAt`, whose `.absent` arm is
   `DescriptorIR2.opensTo` — `∃ h : Heap.FeltHeap, mapRoot hash 16 h = root ∧ …`, an **arity-2**
   `Heap.leafOf` commitment. The deployed map tree is an **arity-3** IMT (`descriptor_ir2.rs`
   `map_leaf_input_cols = [MAP_KEY, value_col, MAP_NEXT]`, "IMT leaf `hash[addr, value, next_addr]`
   (arity 2 → 3)") — for EVERY map-op kind, not just `.absent`. §1 proves that under the single
   named `Poseidon2SpongeCR` floor those are DIFFERENT commitments at the same felt
   (`imtRoot_ne_mapRoot`), hence at a deployed pre-root:
     * `opensToMerkle` / `writesToMerkle` have NO witness (`opensToMerkle_unsat_at_imtRoot`,
       `writesToMerkle_unsat_at_imtRoot`);
     * `ReconcileGatesAt` has no witness FOR ANY KIND (`reconcileGatesAt_unsat_at_imtRoot`) — so the
       apex premise is not merely incomplete in the top gap, it is EMPTY on every deployed row;
     * and `MapOp.holdsAt` — the DENOTATION the apex concludes about — has no witness either
       (`mapOpHoldsAt_unsat_at_imtRoot`).
   The last one is the wall: no premise whatsoever can deliver a conclusion that is itself refutable
   at the deployed commitment. Repointing the apex therefore requires moving `opensTo`/`writesTo`
   (hence `MapOp.holdsAt`, `VmConstraint2.holdsAt`, `Satisfied2`, `AlgoStarkSound`) onto the IMT
   commitment — a DENOTATION change, strictly larger than the named REMAINING WIRE and out of scope
   for an additive module.

## ⚑ THE ASSESSMENT OF THE NAMED REMAINING WIRE (`MapOpsColumnLayout` §8): NOT REQUIRED, AND
   NOT SUFFICIENT

The scoping guess was that the digest-vector → chain-symbol bridge is what stands between the
repointed dispatch and the apex's `∃ h` slot. It is neither:

  * NOT REQUIRED for the repointing: `AbsentRowImtAt` carries the chain symbol in the same slot
    `ReconcileGatesAt`'s `∃ h, Heap.SortedKeys h` occupies — a per-deployment knowledge-extraction
    premise of the same species, not a new floor. §4 discharges it CONCRETELY on the witness spine.
  * NOT SUFFICIENT for the apex: `imtRootedRow_wire_does_not_reach_the_heap_slot` shows that even
    GIVEN the chain symbol `c` behind the pre-root, the `∃ h : Heap.FeltHeap` slot is UNREACHABLE —
    the projection `imtToHeap c` is a perfectly good sorted heap of the right size, but its `mapRoot`
    is provably NOT the row's root column. The obstruction is the LEAF ARITY of the slot, which no
    wire between the digest vector and the chain symbol can change.

`ImtSorted` is NOT promoted to a floor anywhere here: it rides in the `∃ h` slot, exactly as
`MapAbsentImtGate` carries it. `Poseidon2SpongeCR` is the only named floor; no new one is added.

## ⚠ TWO RESIDUALS, NAMED (neither claimed closed)

  1. **NO PADDING — the same seam `MapAbsentImtGateWide` already carries.** Every statement here is
     at the UNPADDED commitment form `perfectRoot hash dep (c.map (imtLeafHash hash))`: the chain IS
     the committed vector. The deployment pads a `2 ^ HEAP_TREE_DEPTH` vector with an empty-slot
     sentinel (`IndexedMerkleTree.imtLayout` / `ImtVecCorr` / `PreRootModelsChain` are the existing
     bridge), so the wall theorems apply verbatim to the padded root only once the index-0 step is
     redone there. It goes through for the deployed layout — position 0 always holds a REAL leaf (the
     MIN sentinel), whose digest is arity-3 — but that is NOT proved here, and the wall is therefore
     stated at the form the epoch's `.absent` family already sits on, not at `imtLayout`.
  2. **The repointed dispatch is not wired into any apex assembler.** It cannot be, for the reason
     in finding 2; `mapOpsArmImt_of_modeler` is where the chain stops. Nothing downstream of
     `AlgoStarkSoundFanoutMemory` consumes anything from this file yet.

## What this file authors (ADDITIVE — `ReconcileGatesAt` and every adjacency-shaped theorem stand)

  * **§1 THE ROOT-LEVEL ARITY WALL** — `imtRoot_ne_mapRoot` lifts `imtLeafHash_ne_heapLeafOf` from
    leaves to ROOTS, and the four consequences above, plus
    `mapReconcileModelOk_forbids_imtRootedRows`: the apex's carried premise, read at deployed depth,
    says NO fired map-op row's pre-root is EVER the deployed indexed-Merkle commitment.
  * **§2 THE REPOINTED DISPATCH** — `AbsentRowImtAt` / `ReconcileGatesImtAt` /
    `MapReconcileImtModelOk`, the repointed `.absent` denotation `imtOpensNone` at the DEPLOYED
    commitment, the per-row law, the projected-root bridge (both commitments named, never
    conflated), the repointed arm `mapOpsArmImt_of_modeler`, and the two-directional
    INCOMPARABILITY of the two models on concrete rows.
  * **§3 THE DEPLOYED-DEPTH WITNESS KIT** — `spineC`, its length / sortedness / address bound, the
    doubling split `spineC_add`, and `spineC_open_last`: a membership path to the perfect-tree root
    at SYMBOLIC depth. This is what lets §4 land at `MAP_TREE_DEPTH` instead of at a toy depth.
  * **§4 THE TOP-GAP EXHIBIT AT THE DEPLOYED DEPTH** — one descriptor, one trace, one fired
    `.absent` row whose key is the fresh key just above the committed maximum: the OLD model is
    FALSE by TWO independent mechanisms (the arity wall at the deployed IMT root; the bracket, above
    the max, at the counterfactual arity-2 root), the REPOINTED model HOLDS, the repointed law
    fires the absence — and `MapOp.holdsAt` is REFUTED on the same row, which is the wall made
    concrete. The narrow toy witnesses (`topChain`, key `50`) are reused verbatim at the row level.
  * **§5 THE INSTRUMENT** — the finding restated in `PremiseInhabitability`'s vocabulary
    (`Empties` / `AcceptsSome`), so it is comparable with the FRI-side premise-vacuity result.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; sorry-free; no `native_decide`; no
`decide` on any object containing the depth-16 spine. Crypto enters ONLY as `Poseidon2SpongeCR`.
NEW file; every import read-only; no deployed descriptor / emit / JSON / Rust byte touched.

`AlgoStarkSoundFanoutMemory` is deliberately NOT imported: it is RED in this tree for reasons
outside this lane (`noteSpendV3_shape` at line 261 hits `maximum recursion depth`, from concurrent
churn in the `Emit/` descriptors it reads). Its premise `MapReconcileFamily` delivers exactly
`MapOpsColumnLayout.MapReconcileModelOk hash d (tr pi π)` per accepting batch, which is the object
every theorem here is stated over, so the composition is a one-liner once that module is repaired.
-/
import Dregg2.Circuit.MapAbsentImtGate
import Dregg2.Circuit.PremiseInhabitability

namespace Dregg2.Circuit.MapReconcileImtRepoint

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.MapMerkleRoot (mapNode perfectRoot perfectRoot_injective
  mapRoot mapRoot_injective opensToMerkle writesToMerkle)
open Dregg2.Circuit.MapOpsColumnLayout (pathRecompute perfectRoot_append ReconcileGatesAt
  MapReconcileModelOk mapOp_holds_of_mapReconcile mem_mapOpsOf toyAbsentOp toyAbsentEnv toyHeap
  toy_absent_gates)
open Dregg2.Circuit.IndexedMerkleTree (ImtLeaf ImtSorted imtAddrs imtAddrs_cons imtToHeap
  imtLeafHash imtSorted_sortedKeys keys_imtToHeap)
open Dregg2.Circuit.MapAbsentImtGate (AbsentImtGatesAt absentImtGates_force_absence
  imtLeafHash_ne_heapLeafOf AdjacentBracketGates adjacentBracket_unsat_above_max
  topChain topChain_sorted topRoot topGap_deployed_accepts)
open Dregg2.Substrate

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 — THE ROOT-LEVEL ARITY WALL.

`MapAbsentImtGate.imtLeafHash_ne_heapLeafOf` separates the two LEAF digests (arity 3 vs arity 2).
Composed with `perfectRoot_injective` that separation lifts to the ROOTS: a committed indexed-Merkle
pre-root is never the `mapRoot` of ANY heap of the same size. Everything the deployed `Ir2Air::MapOps`
row is asserted to satisfy in Lean — the extraction premise, the openings, the denotation — lives on
the arity-2 side, so all of it is refuted at a deployed pre-root. -/

/-- **★ THE ARITY SEPARATION, AT THE ROOT.** Under the one named CR floor, the depth-`dep`
perfect-tree fold of an IMT chain's arity-3 leaf digests is NEVER the `mapRoot` of an arity-2 heap of
the same size: equal roots would force equal leaf-digest vectors (`perfectRoot_injective`), hence an
arity-3 digest equal to an arity-2 digest at position 0 (`imtLeafHash_ne_heapLeafOf`). The deployed
`heap_root.rs` tree and the Lean `mapRoot` denotation are DIFFERENT commitments. -/
theorem imtRoot_ne_mapRoot (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (dep : Nat)
    (c : List ImtLeaf) (h : Heap.FeltHeap)
    (hc : c.length = 2 ^ dep) (hh : h.length = 2 ^ dep) :
    perfectRoot hash dep (c.map (imtLeafHash hash)) ≠ mapRoot hash dep h := by
  intro heq
  have hvec : c.map (imtLeafHash hash) = h.map (Heap.leafOf hash) :=
    perfectRoot_injective hash dep (by rw [List.length_map]; exact hc)
      (by rw [List.length_map]; exact hh) (fun hcc => hcc.1 (hCR _ _ hcc.2)) heq
  have hposc : 0 < c.length := by rw [hc]; exact Nat.two_pow_pos dep
  have hposh : 0 < h.length := by rw [hh]; exact Nat.two_pow_pos dep
  have h0 : (c.map (imtLeafHash hash))[0]? = (h.map (Heap.leafOf hash))[0]? := by rw [hvec]
  rw [List.getElem?_map, List.getElem?_map, List.getElem?_eq_getElem hposc,
    List.getElem?_eq_getElem hposh] at h0
  simp only [Option.map_some, Option.some.injEq] at h0
  exact imtLeafHash_ne_heapLeafOf hash hCR c[0] h[0] h0

/-- At a deployed indexed-Merkle pre-root the arity-2 OPENING has no witness — for any key and any
claimed read. -/
theorem opensToMerkle_unsat_at_imtRoot (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (dep : Nat)
    (c : List ImtLeaf) (hc : c.length = 2 ^ dep) (k : ℤ) (o : Option ℤ) :
    ¬ opensToMerkle hash dep (perfectRoot hash dep (c.map (imtLeafHash hash))) k o := by
  rintro ⟨h, -, hlen, hroot, -⟩
  exact imtRoot_ne_mapRoot hash hCR dep c h hc hlen hroot.symm

/-- …and neither does the arity-2 WRITE. -/
theorem writesToMerkle_unsat_at_imtRoot (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (dep : Nat) (c : List ImtLeaf) (hc : c.length = 2 ^ dep) (k v r' : ℤ) :
    ¬ writesToMerkle hash dep (perfectRoot hash dep (c.map (imtLeafHash hash))) k v r' := by
  rintro ⟨h, -, hlen, -, hroot, -⟩
  exact imtRoot_ne_mapRoot hash hCR dep c h hc hlen hroot.symm

/-- **★ THE OLD PER-ROW BODY IS UNSATISFIABLE AT A DEPLOYED PRE-ROOT — FOR EVERY OP KIND.**
`ReconcileGatesAt` carries its arity-2 heap extraction premise OUTSIDE the per-kind match, so the
refutation does not even reach the gates: a row whose pre-root column is the deployed indexed-Merkle
commitment admits NO gate data, `.read` / `.absent` / `.write` / `.insert` / `.aafiInsert` alike.
This is strictly wider than the top-gap `.absent` incompleteness — that one bites the SHAPE of the
bracket, this one bites the COMMITMENT of every row. -/
theorem reconcileGatesAt_unsat_at_imtRoot (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (dep : Nat) (a : Assignment) (m : MapOp) (c : List ImtLeaf) (hc : c.length = 2 ^ dep)
    (hrow : (m.root 0).eval a = perfectRoot hash dep (c.map (imtLeafHash hash))) :
    ¬ ReconcileGatesAt hash dep a m := by
  rintro ⟨h, -, hlen, hroot, -⟩
  exact imtRoot_ne_mapRoot hash hCR dep c h hc hlen (hrow.symm.trans hroot.symm)

/-- **★ THE WALL: THE DENOTATION ITSELF IS REFUTED AT A DEPLOYED PRE-ROOT.** `MapOp.holdsAt` — what
`Satisfied2`'s `.mapOp` arm asserts and what every apex theorem concludes about — speaks `opensTo` /
`writesTo`, i.e. the arity-2 commitment, at the ROW's pre-root column. On a fired row whose pre-root
is the deployed indexed-Merkle commitment it is FALSE for every kind. **Hence no repointing of the
PREMISE can make the apex non-vacuous there: its CONCLUSION is refutable at the deployed commitment.
The denotation has to move.** -/
theorem mapOpHoldsAt_unsat_at_imtRoot (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (env : VmRowEnv) (m : MapOp) (c : List ImtLeaf) (hc : c.length = 2 ^ MAP_TREE_DEPTH)
    (hguard : m.guard.eval env.loc = 1)
    (hrow : (m.root 0).eval env.loc
      = perfectRoot hash MAP_TREE_DEPTH (c.map (imtLeafHash hash))) :
    ¬ MapOp.holdsAt hash env m := by
  intro hh
  have h := hh hguard
  rw [hrow] at h
  cases hop : m.op with
  | read =>
    rw [hop] at h
    exact opensToMerkle_unsat_at_imtRoot hash hCR MAP_TREE_DEPTH c hc _ _ h.1
  | absent =>
    rw [hop] at h
    exact opensToMerkle_unsat_at_imtRoot hash hCR MAP_TREE_DEPTH c hc _ _ h.1
  | write =>
    rw [hop] at h
    exact writesToMerkle_unsat_at_imtRoot hash hCR MAP_TREE_DEPTH c hc _ _ _ h
  | insert =>
    rw [hop] at h
    exact writesToMerkle_unsat_at_imtRoot hash hCR MAP_TREE_DEPTH c hc _ _ _ h
  | aafiInsert =>
    rw [hop] at h
    exact writesToMerkle_unsat_at_imtRoot hash hCR MAP_TREE_DEPTH c hc _ _ _ h

/-- **★ THE APEX PREMISE, READ AT DEPLOYED DEPTH, FORBIDS THE DEPLOYED COMMITMENT.**
`AlgoStarkSoundFanoutMemory.MapReconcileFamily` delivers exactly this predicate per accepting batch.
What it says, unpacked: on every fired declared map-op row, the pre-root column is NOT the
indexed-Merkle root of ANY committed chain — i.e. the premise holds only on traces the deployed
`heap_root.rs` prover does not produce. That is the vacuity, stated without needing an accepting
pole. -/
theorem mapReconcileModelOk_forbids_imtRootedRows (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash) (d : EffectVmDescriptor2) (t : VmTrace)
    (hok : MapReconcileModelOk hash d t) :
    ∀ i < t.rows.length, ∀ m ∈ mapOpsOf d, m.guard.eval (envAt t i).loc = 1 →
      ∀ c : List ImtLeaf, c.length = 2 ^ MAP_TREE_DEPTH →
        (m.root 0).eval (envAt t i).loc
          ≠ perfectRoot hash MAP_TREE_DEPTH (c.map (imtLeafHash hash)) :=
  fun i hi m hm hg c hc hrow =>
    reconcileGatesAt_unsat_at_imtRoot hash hCR MAP_TREE_DEPTH (envAt t i).loc m c hc hrow
      (hok i hi m hm hg)

/-! ## §2 — THE REPOINTED DISPATCH.

The `.absent` arm is judged by the shape that ships. The chain symbol rides in the SAME
knowledge-extraction slot `ReconcileGatesAt`'s `∃ h, Heap.SortedKeys h` occupies — same species, no
new floor, and `ImtSorted` is not promoted anywhere. Every other kind is left EXACTLY as it was, so
the adjacency arm remains available for the future model in which the AIR really does open two
adjacent leaves (`MapAbsentImtGate.interior_pointerBracket_iff_adjacent` shows the two agree on the
interior). -/

/-- **`AbsentRowImtAt`** — the deployed `Ir2Air::MapAbsent` acceptance AT THE ROW'S COLUMNS: the
committed `ImtSorted` chain behind the pre-root column (the extraction premise, NAMED), plus the
deployed gate `MapAbsentImtGate.AbsentImtGatesAt` on `(root, new_root, key)` as the row evaluates
them. No second leaf and no `pathPos` adjacency — the deployed table has neither. -/
def AbsentRowImtAt (hash : List ℤ → ℤ) (dep : Nat) (a : Assignment) (m : MapOp) : Prop :=
  ∃ (c : List ImtLeaf) (lowAddr lowValue lowNext : ℤ),
    ImtSorted c ∧
    c.length = 2 ^ dep ∧
    (m.root 0).eval a = perfectRoot hash dep (c.map (imtLeafHash hash)) ∧
    AbsentImtGatesAt hash dep ((m.root 0).eval a) ((m.newRoot 0).eval a) (m.key.eval a)
      lowAddr lowValue lowNext

/-- **`ReconcileGatesImtAt`** — `ReconcileGatesAt` with the `.absent` dispatch REPOINTED, written as
two guarded arms so the dispatch is visible in the statement: an `.absent` row is judged by the
DEPLOYED shape, every other kind by the original body, verbatim. -/
def ReconcileGatesImtAt (hash : List ℤ → ℤ) (dep : Nat) (a : Assignment) (m : MapOp) : Prop :=
  (m.op = MapOpKind.absent → AbsentRowImtAt hash dep a m) ∧
  (m.op ≠ MapOpKind.absent → ReconcileGatesAt hash dep a m)

theorem reconcileGatesImt_absent (hash : List ℤ → ℤ) (dep : Nat) (a : Assignment) (m : MapOp)
    (hop : m.op = MapOpKind.absent) :
    ReconcileGatesImtAt hash dep a m ↔ AbsentRowImtAt hash dep a m :=
  ⟨fun h => h.1 hop, fun h => ⟨fun _ => h, fun hne => absurd hop hne⟩⟩

theorem reconcileGatesImt_of_ne_absent (hash : List ℤ → ℤ) (dep : Nat) (a : Assignment) (m : MapOp)
    (hop : m.op ≠ MapOpKind.absent) :
    ReconcileGatesImtAt hash dep a m ↔ ReconcileGatesAt hash dep a m :=
  ⟨fun h => h.2 hop, fun h => ⟨fun habs => absurd habs hop, fun _ => h⟩⟩

/-- **The per-trace REPOINTED model** — the drop-in twin of
`MapOpsColumnLayout.MapReconcileModelOk`, at the same deployed depth. -/
def MapReconcileImtModelOk (hash : List ℤ → ℤ) (d : EffectVmDescriptor2) (t : VmTrace) : Prop :=
  ∀ i < t.rows.length, ∀ m ∈ mapOpsOf d,
    m.guard.eval (envAt t i).loc = 1 → ReconcileGatesImtAt hash MAP_TREE_DEPTH (envAt t i).loc m

/-- **`imtOpensNone hash dep r k`** — the `.absent` DENOTATION at the DEPLOYED commitment: some
committed `ImtSorted` chain behind the indexed-Merkle pre-root `r` holds no entry at `k`. The
repointed replacement for `opensTo … none`; the two are not comparable, they are openings of
different commitments (§1). -/
def imtOpensNone (hash : List ℤ → ℤ) (dep : Nat) (r k : ℤ) : Prop :=
  ∃ c : List ImtLeaf, ImtSorted c ∧ c.length = 2 ^ dep ∧
    r = perfectRoot hash dep (c.map (imtLeafHash hash)) ∧
    k ∉ imtAddrs c ∧ Heap.get (imtToHeap c) k = none

/-- **★ THE REPOINTED PER-ROW LAW.** An accepting DEPLOYED `.absent` row forces the row's key off the
whole committed address spine and `Heap.get` on the projected map to be `none`, and the post-root
column to equal the pre-root column. `MapAbsentImtGate.absentImtGates_force_absence` composed with
the row's own columns — nothing re-derived. -/
theorem absentRowImt_force_imtOpensNone (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (dep : Nat) (a : Assignment) (m : MapOp) (hg : AbsentRowImtAt hash dep a m) :
    imtOpensNone hash dep ((m.root 0).eval a) (m.key.eval a)
      ∧ (m.newRoot 0).eval a = (m.root 0).eval a := by
  obtain ⟨c, lowAddr, lowValue, lowNext, hs, hlen, hroot, hgate⟩ := hg
  obtain ⟨hnotin, hget, hnr⟩ := absentImtGates_force_absence hash hCR dep hs hlen hroot hgate
  exact ⟨⟨c, hs, hlen, hroot, hnotin, hget⟩, hnr⟩

/-- **THE TWO COMMITMENTS, NAMED — never conflated.** The repointed absence DOES yield an ordinary
`opensToMerkle … none`, but at the PROJECTED map root of the chain, which §1 proves is a different
felt from the row's pre-root column. Any consumer that wants the arity-2 opening must carry both
roots, exactly as `MapAbsentImtGateWide.absentImtGatesW_force_keysOfW_absence` does on the wide
side. -/
theorem imtOpensNone_gives_projected_opening (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (dep : Nat) {r k : ℤ} (h : imtOpensNone hash dep r k) :
    ∃ c : List ImtLeaf, ImtSorted c ∧ c.length = 2 ^ dep ∧
      r = perfectRoot hash dep (c.map (imtLeafHash hash)) ∧
      opensToMerkle hash dep (mapRoot hash dep (imtToHeap c)) k none ∧
      mapRoot hash dep (imtToHeap c) ≠ r := by
  obtain ⟨c, hs, hlen, hroot, hnotin, hget⟩ := h
  have hplen : (imtToHeap c).length = 2 ^ dep := by
    rw [imtToHeap, List.length_map]; exact hlen
  refine ⟨c, hs, hlen, hroot, ⟨imtToHeap c, imtSorted_sortedKeys hs, hplen, rfl, hget⟩, ?_⟩
  rw [hroot]
  exact fun hcon => imtRoot_ne_mapRoot hash hCR dep c (imtToHeap c) hlen hplen hcon.symm

/-- **★ THE NAMED REMAINING WIRE IS NOT SUFFICIENT.** Even GIVEN the chain symbol behind the
pre-root — which is exactly what the digest-vector → chain-symbol bridge would supply — the
`∃ h : Heap.FeltHeap` slot of `ReconcileGatesAt` stays UNREACHABLE: the projection `imtToHeap c` is a
perfectly good sorted heap of the right size, and its `mapRoot` is still not the row's pre-root. The
obstruction is the leaf ARITY of the slot, which no such wire touches. -/
theorem imtRootedRow_wire_does_not_reach_the_heap_slot (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash) (dep : Nat) (a : Assignment) (m : MapOp) (c : List ImtLeaf)
    (hs : ImtSorted c) (hlen : c.length = 2 ^ dep)
    (hrow : (m.root 0).eval a = perfectRoot hash dep (c.map (imtLeafHash hash))) :
    Heap.SortedKeys (imtToHeap c) ∧ (imtToHeap c).length = 2 ^ dep ∧
      mapRoot hash dep (imtToHeap c) ≠ (m.root 0).eval a ∧
      ¬ ReconcileGatesAt hash dep a m := by
  have hplen : (imtToHeap c).length = 2 ^ dep := by
    rw [imtToHeap, List.length_map]; exact hlen
  refine ⟨imtSorted_sortedKeys hs, hplen, ?_,
    reconcileGatesAt_unsat_at_imtRoot hash hCR dep a m c hlen hrow⟩
  rw [hrow]
  exact fun hcon => imtRoot_ne_mapRoot hash hCR dep c (imtToHeap c) hlen hplen hcon.symm

/-- **`MapOpImtHoldsAt`** — the per-row denotation with the `.absent` arm moved to the deployed
commitment and every other arm left exactly as `MapOp.holdsAt` states it. The object a repointed
`Satisfied2` would have to be stated over. -/
def MapOpImtHoldsAt (hash : List ℤ → ℤ) (env : VmRowEnv) (m : MapOp) : Prop :=
  (m.op = MapOpKind.absent → m.guard.eval env.loc = 1 →
      imtOpensNone hash MAP_TREE_DEPTH ((m.root 0).eval env.loc) (m.key.eval env.loc)
        ∧ (m.newRoot 0).eval env.loc = (m.root 0).eval env.loc) ∧
  (m.op ≠ MapOpKind.absent → MapOp.holdsAt hash env m)

/-- **★ THE REPOINTED `.mapOp` ARM (∀ d).** The repointed model + the one CR floor force the
repointed per-row denotation for every declared map op: the `.absent` rows through the deployed
pointer-bracket law, every other kind through the untouched `mapOp_holds_of_mapReconcile`. This is
`MapOpsColumnLayout.mapOpsArm_of_modeler` with the `.absent` leg moved onto the shape that ships —
and it is exactly as far as the repointing can go before it meets the wall of §1, because
`MemoryLegs` demands `MapOp.holdsAt`, not this. -/
theorem mapOpsArmImt_of_modeler (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (d : EffectVmDescriptor2) (t : VmTrace) (hok : MapReconcileImtModelOk hash d t) :
    ∀ i < t.rows.length, ∀ m : MapOp, VmConstraint2.mapOp m ∈ d.constraints →
      MapOpImtHoldsAt hash (envAt t i) m := by
  intro i hi m hm
  have hmem : m ∈ mapOpsOf d := mem_mapOpsOf.mpr hm
  have hmodel : m.guard.eval (envAt t i).loc = 1 →
      ReconcileGatesImtAt hash MAP_TREE_DEPTH (envAt t i).loc m := hok i hi m hmem
  refine ⟨fun hop hguard => ?_, fun hop => ?_⟩
  · exact absentRowImt_force_imtOpensNone hash hCR MAP_TREE_DEPTH (envAt t i).loc m
      ((hmodel hguard).1 hop)
  · exact mapOp_holds_of_mapReconcile hash hCR (envAt t i) m
      (fun hguard => (hmodel hguard).2 hop)

/-! ## §3 — THE DEPLOYED-DEPTH WITNESS KIT.

Everything above is depth-generic; the exhibit below must land at the DEPLOYED depth, because that
is where `MapReconcileModelOk` is stated (`MAP_TREE_DEPTH = 16`) — the existing top-gap witnesses are
at depth 2 and 1 and do NOT instantiate it. A depth-16 witness needs a `2^16`-leaf sorted chain AND a
membership path into its root, with nothing ever evaluated.

`spineC n a` is the ascending chain `a, a+2, …, a+2(n-1)`, each leaf pointing at the NEXT address —
so the LAST leaf's pointer `a + 2n` is a terminal `SENTINEL_MAX` face that is NOT a stored address,
exactly the deployed shape, and the interval `(a + 2n - 2, a + 2n)` is the TOP GAP. The cons
recursion gives sortedness in three lines; `spineC_add` splits it at ANY point, which is what lets
`spineC_open_last` build the path by the same doubling `perfectRoot_append` folds by. -/

/-- The ascending deployed-shape spine: `n` leaves at addresses `a, a+2, …`, each pointing at the
next. Never evaluated at the deployed `n = 2 ^ 16`; every fact below is proved by induction on `n`. -/
def spineC : Nat → ℤ → List ImtLeaf
  | 0, _ => []
  | n + 1, a => ⟨a, 0, a + 2⟩ :: spineC n (a + 2)

theorem spineC_length : ∀ (n : Nat) (a : ℤ), (spineC n a).length = n := by
  intro n
  induction n with
  | zero => intro a; rfl
  | succ n ih => intro a; simp only [spineC, List.length_cons, ih]

/-- **The spine SPLITS anywhere** — the doubling identity `spineC (m+n) a = spineC m a ++ spineC n
(a + 2m)`, which at `m = n = 2^d` lines the chain up with the perfect tree's top node. -/
theorem spineC_add : ∀ (m n : Nat) (a : ℤ),
    spineC (m + n) a = spineC m a ++ spineC n (a + 2 * (m : ℤ)) := by
  intro m
  induction m with
  | zero =>
    intro n a
    simp only [spineC, Nat.zero_add, Nat.cast_zero, mul_zero, add_zero, List.nil_append]
  | succ m ih =>
    intro n a
    have hidx : m + 1 + n = (m + n) + 1 := by omega
    rw [hidx]
    simp only [spineC, List.cons_append]
    rw [ih n (a + 2)]
    congr 2
    push_cast
    ring

theorem spineC_sorted : ∀ (n : Nat) (a : ℤ), ImtSorted (spineC n a) := by
  intro n
  induction n with
  | zero => intro a; trivial
  | succ n ih =>
    intro a
    cases n with
    | zero => show (a : ℤ) < a + 2; linarith
    | succ m =>
      show ImtSorted ((⟨a, 0, a + 2⟩ : ImtLeaf) :: (⟨a + 2, 0, a + 2 + 2⟩ : ImtLeaf)
        :: spineC m (a + 2 + 2))
      exact ⟨by linarith, rfl, ih (a + 2)⟩

/-- Every committed address of the spine is at or below `a + 2n - 2` — so every key in the terminal
gap `(a + 2n - 2, a + 2n)` is ABOVE the committed maximum. That is the ordinary path: a fresh
nullifier / cell-id lands there on every turn. -/
theorem spineC_addr_le : ∀ (n : Nat) (a : ℤ),
    ∀ x ∈ imtAddrs (spineC n a), x ≤ a + 2 * (n : ℤ) - 2 := by
  intro n
  induction n with
  | zero => intro a x hx; simp only [spineC, imtAddrs] at hx; simp at hx
  | succ n ih =>
    intro a x hx
    simp only [spineC, imtAddrs_cons] at hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · have hn : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
      push_cast
      linarith
    · have := ih (a + 2) x hx'
      push_cast at this ⊢
      linarith

/-- **★ THE MEMBERSHIP PATH AT SYMBOLIC DEPTH.** For every depth `d`, the LAST leaf of the
`2^d`-leaf spine has a length-`d` Merkle path recomputing to the spine's perfect-tree root. Built by
the same doubling the tree folds by (`spineC_add` at `2^d + 2^d`, then `perfectRoot_append`), so
nothing is enumerated: at `d = 16` this produces the deployed-depth opening with no `2^16`-element
object in sight. -/
theorem spineC_open_last (hash : List ℤ → ℤ) : ∀ (d : Nat) (a : ℤ),
    ∃ steps : List (Bool × ℤ), steps.length = d ∧
      pathRecompute hash (imtLeafHash hash ⟨a + 2 * 2 ^ d - 2, 0, a + 2 * 2 ^ d⟩) steps
        = perfectRoot hash d ((spineC (2 ^ d) a).map (imtLeafHash hash)) := by
  intro d
  induction d with
  | zero =>
    intro a
    refine ⟨[], rfl, ?_⟩
    have h1 : a + 2 * 2 ^ (0 : Nat) - 2 = a := by norm_num
    have h2 : a + 2 * 2 ^ (0 : Nat) = a + 2 := by norm_num
    rw [h1, h2]
    rfl
  | succ d ih =>
    intro a
    obtain ⟨steps, hlen, hrec⟩ := ih (a + 2 * 2 ^ d)
    have h1 : a + 2 * 2 ^ (d + 1) - 2 = (a + 2 * 2 ^ d) + 2 * 2 ^ d - 2 := by ring
    have h2 : a + 2 * 2 ^ (d + 1) = (a + 2 * 2 ^ d) + 2 * 2 ^ d := by ring
    have hsplit : spineC (2 ^ (d + 1)) a
        = spineC (2 ^ d) a ++ spineC (2 ^ d) (a + 2 * 2 ^ d) := by
      have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by ring
      have hcast : (2 : ℤ) * ((2 ^ d : ℕ) : ℤ) = 2 * 2 ^ d := by push_cast; ring
      rw [hpow, spineC_add, hcast]
    have hL : ((spineC (2 ^ d) a).map (imtLeafHash hash)).length = 2 ^ d := by
      rw [List.length_map, spineC_length]
    have hR : ((spineC (2 ^ d) (a + 2 * 2 ^ d)).map (imtLeafHash hash)).length = 2 ^ d := by
      rw [List.length_map, spineC_length]
    refine ⟨(true, perfectRoot hash d ((spineC (2 ^ d) a).map (imtLeafHash hash))) :: steps,
      by simp only [List.length_cons, hlen], ?_⟩
    rw [h1, h2]
    simp only [pathRecompute]
    rw [hrec, hsplit, List.map_append, perfectRoot_append hash d _ _ hL hR]

/-! ## §4 — THE TOP-GAP EXHIBIT AT THE DEPLOYED DEPTH.

One descriptor (`toyAbsentOp` on wires 0/1/2/3, always-firing guard — the epoch's own row vehicle),
one row, one fresh key `2 + 2·2^16 - 1` sitting in the terminal gap above every committed address.
This is an ORDINARY row: every fresh nullifier / cell-id above the current maximum lands here. -/

section Exhibit

open Dregg2.Circuit.Poseidon2Binding.Reference (refSponge refSponge_CR)

/-! ### §4a — the WITNESS CHAIN at the deployed depth.

⚠ MECHANICAL DISCIPLINE, load-bearing: `MAP_TREE_DEPTH` is a REDUCIBLE abbreviation of a literal, so
any `rfl` between a `perfectRoot`-headed term and a *definition* whose body is that term invites the
elaborator to whnf `perfectRoot hash 16 (…)` — which enumerates the `2^16` spine and dies at the
heartbeat limit (it did, on the first pass). Everything below therefore (i) spells the pre-root
INLINE so both sides of every equation are `perfectRoot`-headed, and (ii) reads the row's columns only
through the four `rowOf_*` lemmas, which are `rfl`s over FREE VARIABLES. -/

/-- The deployed depth's leaf count, as an integer. Never evaluated. -/
def depT : ℤ := 2 ^ MAP_TREE_DEPTH

/-- The committed chain behind the row's pre-root: the `2 ^ 16`-leaf ascending spine. -/
def depSpine : List ImtLeaf := spineC (2 ^ MAP_TREE_DEPTH) 2

/-- The fresh key, in the terminal gap: above EVERY committed address, below the terminal pointer.
This is the ordinary path — every fresh nullifier / cell-id above the current maximum lands here. -/
def depKey : ℤ := 2 + 2 * depT - 1

theorem depSpine_length : depSpine.length = 2 ^ MAP_TREE_DEPTH := spineC_length _ _

theorem depSpine_sorted : ImtSorted depSpine := spineC_sorted _ _

theorem depHeap_length : (imtToHeap depSpine).length = 2 ^ MAP_TREE_DEPTH := by
  simp only [imtToHeap, List.length_map]
  exact depSpine_length

theorem depSpine_addr_lt : ∀ x ∈ imtAddrs depSpine, x < depKey := by
  intro x hx
  have h := spineC_addr_le (2 ^ MAP_TREE_DEPTH) 2 x hx
  simp only [depKey, depT]
  push_cast at h ⊢
  linarith

/-- **The deployed gate ACCEPTS the honest top-gap row, AT THE DEPLOYED DEPTH.** The last leaf's
terminal pointer brackets the fresh key, ONE arity-3 path authenticates the low leaf (from
`spineC_open_last`, so no `2^16` object is enumerated), the root is preserved. Over an ARBITRARY
hash — this is an ordinary row, not a shape. -/
theorem depGate_accepts (hash : List ℤ → ℤ) :
    AbsentImtGatesAt hash MAP_TREE_DEPTH
      (perfectRoot hash MAP_TREE_DEPTH (depSpine.map (imtLeafHash hash)))
      (perfectRoot hash MAP_TREE_DEPTH (depSpine.map (imtLeafHash hash)))
      depKey (2 + 2 * depT - 2) 0 (2 + 2 * depT) := by
  obtain ⟨steps, hslen, hrec⟩ := spineC_open_last hash MAP_TREE_DEPTH 2
  refine ⟨depSpine.map (imtLeafHash hash), steps, ?_, hslen, rfl, ?_, ?_, ?_, rfl⟩
  · rw [List.length_map]; exact depSpine_length
  · simpa only [depT, depSpine] using hrec
  · simp only [depKey]; linarith
  · simp only [depKey]; linarith

/-! ### §4b — the row vehicle: ONE fired `.absent` op, PARAMETRIC in the pre-root felt. -/

/-- The one-row descriptor carrying a single fired `.absent` map op (`toyAbsentOp` — the epoch's own
row vehicle: `root`/`key`/`value`/`new_root` on wires 0/1/2/3, always-firing guard). -/
def dTopGap : EffectVmDescriptor2 :=
  { name := "map-absent-top-gap"
  , traceWidth := 4
  , piCount := 0
  , tables := []
  , constraints := [VmConstraint2.mapOp toyAbsentOp]
  , hashSites := []
  , ranges := [] }

theorem dTopGap_mapOps : mapOpsOf dTopGap = [toyAbsentOp] := rfl

theorem mem_dTopGap {m : MapOp} (h : m ∈ mapOpsOf dTopGap) : m = toyAbsentOp := by
  rw [dTopGap_mapOps] at h
  simpa using h

/-- The row: pre-root and post-root columns carry `r`, the key column `k`. PARAMETRIC on purpose
(see §4a's discipline note). -/
def rowOf (r k : ℤ) : Assignment := fun c =>
  if c = 0 then r else if c = 1 then k else if c = 2 then 0 else if c = 3 then r else 0

/-- The one-row trace over that row. -/
def traceOf (r k : ℤ) : VmTrace :=
  { rows := [rowOf r k], pub := fun _ => 0, tf := fun _ => [] }

theorem traceOf_rows_length (r k : ℤ) : (traceOf r k).rows.length = 1 := rfl
theorem traceOf_loc (r k : ℤ) : (envAt (traceOf r k) 0).loc = rowOf r k := rfl
theorem rowOf_root (r k : ℤ) : (toyAbsentOp.root 0).eval (rowOf r k) = r := rfl
theorem rowOf_newRoot (r k : ℤ) : (toyAbsentOp.newRoot 0).eval (rowOf r k) = r := rfl
theorem rowOf_key (r k : ℤ) : toyAbsentOp.key.eval (rowOf r k) = k := rfl
theorem rowOf_guard (r k : ℤ) : toyAbsentOp.guard.eval (rowOf r k) = 1 := rfl

/-! ### §4c — the two halves, ROW-GENERIC first (any hash, any chain, deployed depth). -/

/-- **The repointed dispatch, row-generic**: an accepting DEPLOYED gate over a committed `ImtSorted`
chain IS a repointed `.absent` row body at the row that carries that chain's pre-root. -/
theorem rowOf_reconcileGatesImt (hash : List ℤ → ℤ) (dep : Nat) (c : List ImtLeaf)
    (lowAddr lowValue lowNext k : ℤ) (hs : ImtSorted c) (hlen : c.length = 2 ^ dep)
    (hg : AbsentImtGatesAt hash dep (perfectRoot hash dep (c.map (imtLeafHash hash)))
      (perfectRoot hash dep (c.map (imtLeafHash hash))) k lowAddr lowValue lowNext) :
    ReconcileGatesImtAt hash dep
      (rowOf (perfectRoot hash dep (c.map (imtLeafHash hash))) k) toyAbsentOp := by
  refine ⟨fun _ => ⟨c, lowAddr, lowValue, lowNext, hs, hlen, ?_, ?_⟩, fun hne => absurd rfl hne⟩
  · rw [rowOf_root]
  · rw [rowOf_root, rowOf_newRoot, rowOf_key]
    exact hg

/-- **★ THE REPOINTED PREMISE HOLDS, row-generic at the DEPLOYED depth.** -/
theorem imtRow_model_holds (hash : List ℤ → ℤ) (c : List ImtLeaf)
    (lowAddr lowValue lowNext k : ℤ) (hs : ImtSorted c) (hlen : c.length = 2 ^ MAP_TREE_DEPTH)
    (hg : AbsentImtGatesAt hash MAP_TREE_DEPTH
      (perfectRoot hash MAP_TREE_DEPTH (c.map (imtLeafHash hash)))
      (perfectRoot hash MAP_TREE_DEPTH (c.map (imtLeafHash hash))) k lowAddr lowValue lowNext) :
    MapReconcileImtModelOk hash dTopGap
      (traceOf (perfectRoot hash MAP_TREE_DEPTH (c.map (imtLeafHash hash))) k) := by
  intro i hi m hm hguard
  have hi0 : i = 0 := by rw [traceOf_rows_length] at hi; omega
  subst hi0
  rw [mem_dTopGap hm, traceOf_loc]
  exact rowOf_reconcileGatesImt hash MAP_TREE_DEPTH c lowAddr lowValue lowNext k hs hlen hg

/-- **★ THE OLD PREMISE IS FALSE, row-generic at the DEPLOYED depth** — mechanism A, the
COMMITMENT: at a deployed indexed-Merkle pre-root the old per-row body has no witness at all, its
arity-2 extraction premise being refuted before the gates are read. Note what this does NOT need: no
assumption about the key, the chain's contents, or the op kind. -/
theorem imtRow_old_model_false (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (c : List ImtLeaf) (hlen : c.length = 2 ^ MAP_TREE_DEPTH) (k : ℤ) :
    ¬ MapReconcileModelOk hash dTopGap
        (traceOf (perfectRoot hash MAP_TREE_DEPTH (c.map (imtLeafHash hash))) k) := by
  intro hok
  have hg := hok 0 (by rw [traceOf_rows_length]; omega) toyAbsentOp
    (by rw [dTopGap_mapOps]; exact List.mem_singleton_self _)
    (by rw [traceOf_loc]; exact rowOf_guard _ _)
  refine reconcileGatesAt_unsat_at_imtRoot hash hCR MAP_TREE_DEPTH _ toyAbsentOp c hlen ?_ hg
  rw [traceOf_loc, rowOf_root]

/-! ### §4d — the exhibit, at the CR-PROVED reference sponge. -/

/-- **★ HALF ONE (mechanism A). The OLD apex premise is FALSE on the deployed top-gap row.** -/
theorem topGap_old_model_false :
    ¬ MapReconcileModelOk refSponge dTopGap
        (traceOf (perfectRoot refSponge MAP_TREE_DEPTH (depSpine.map (imtLeafHash refSponge)))
          depKey) :=
  imtRow_old_model_false refSponge refSponge_CR depSpine depSpine_length depKey

/-- **★ HALF ONE (mechanism B — the BRACKET). The OLD premise is FALSE at the top gap even in the
COUNTERFACTUAL arity-2 world**, at the DEPLOYED depth: on the row whose pre-root is the `mapRoot` of
the SAME logical map, the fresh key is above every committed address, so the adjacency arm's hi path
would have to open a committed entry that does not exist. This is
`MapAbsentImtGate.topGap_reconcileGates_unsat` lifted from depth 2 to `MAP_TREE_DEPTH` — the top-gap
incompleteness at the depth the apex premise is actually stated at. -/
theorem topGap_old_model_false_bracket :
    ¬ MapReconcileModelOk refSponge dTopGap
        (traceOf (mapRoot refSponge MAP_TREE_DEPTH (imtToHeap depSpine)) depKey) := by
  intro hok
  have hg := hok 0 (by rw [traceOf_rows_length]; omega) toyAbsentOp
    (by rw [dTopGap_mapOps]; exact List.mem_singleton_self _)
    (by rw [traceOf_loc]; exact rowOf_guard _ _)
  rw [traceOf_loc] at hg
  obtain ⟨h, -, hlen, hroot, hgb, -⟩ := hg
  rw [rowOf_root] at hroot
  rw [rowOf_root, rowOf_key] at hgb
  have hh : h = imtToHeap depSpine :=
    mapRoot_injective refSponge MAP_TREE_DEPTH hlen depHeap_length
      (fun hc => hc.1 (refSponge_CR _ _ hc.2)) hroot
  refine adjacentBracket_unsat_above_max refSponge refSponge_CR MAP_TREE_DEPTH h hlen hroot ?_ hgb
  intro x hx
  rw [hh, keys_imtToHeap] at hx
  exact depSpine_addr_lt x hx

/-- **★ HALF TWO — THE REPOINTED PREMISE HOLDS ON THE SAME ROW.** The deployed-shape dispatch is
satisfied at the deployed depth by the committed spine and its single arity-3 opening: the apex's
carried premise, repointed, is INHABITED exactly where the old one is empty. -/
theorem topGap_imt_model_holds :
    MapReconcileImtModelOk refSponge dTopGap
      (traceOf (perfectRoot refSponge MAP_TREE_DEPTH (depSpine.map (imtLeafHash refSponge)))
        depKey) :=
  imtRow_model_holds refSponge depSpine (2 + 2 * depT - 2) 0 (2 + 2 * depT) depKey
    depSpine_sorted depSpine_length (depGate_accepts refSponge)

/-- **★ AND THE REPOINTED LAW FIRES** — the fresh key is off the whole committed spine and
`Heap.get` on the projected map is `none`. The non-vacuity is not merely of the premise: the
conclusion is delivered on the row. -/
theorem topGap_imt_absence_fires :
    depKey ∉ imtAddrs depSpine
      ∧ Heap.get (imtToHeap depSpine) depKey = none
      ∧ imtOpensNone refSponge MAP_TREE_DEPTH
          (perfectRoot refSponge MAP_TREE_DEPTH (depSpine.map (imtLeafHash refSponge))) depKey := by
  obtain ⟨hnot, hget, -⟩ := absentImtGates_force_absence refSponge refSponge_CR MAP_TREE_DEPTH
    depSpine_sorted depSpine_length rfl (depGate_accepts refSponge)
  exact ⟨hnot, hget, depSpine, depSpine_sorted, depSpine_length, rfl, hnot, hget⟩

/-- **★ THE WALL, CONCRETE ON THE SAME ROW.** `MapOp.holdsAt` — the `.mapOp` arm of `Satisfied2`,
which is what the apex concludes about — is REFUTED here. So the apex conclusion is not recoverable
on this row by ANY repointing of its premise: the DENOTATION is what has to move. -/
theorem topGap_mapOpHoldsAt_false :
    ¬ MapOp.holdsAt refSponge
        (envAt (traceOf
          (perfectRoot refSponge MAP_TREE_DEPTH (depSpine.map (imtLeafHash refSponge))) depKey) 0)
        toyAbsentOp := by
  refine mapOpHoldsAt_unsat_at_imtRoot refSponge refSponge_CR _ toyAbsentOp depSpine
    depSpine_length ?_ ?_
  · rw [traceOf_loc]; exact rowOf_guard _ _
  · rw [traceOf_loc, rowOf_root]

/-- **★ THE TWO MODELS ARE INCOMPARABLE, both directions concrete.** On the deployed row the old
model is empty and the repointed one holds; on the epoch's own arity-2 toy row (key `25` inside the
`20 → 30` gap of `toyHeap`) the old model holds and the repointed one is empty — that row's pre-root
column is a `mapRoot`, which §1 proves is never an indexed-Merkle root. Neither refines the other;
the deployed one is the one that describes the shipped table. -/
theorem models_are_incomparable :
    (¬ MapReconcileModelOk refSponge dTopGap
        (traceOf (perfectRoot refSponge MAP_TREE_DEPTH (depSpine.map (imtLeafHash refSponge)))
          depKey)
      ∧ MapReconcileImtModelOk refSponge dTopGap
        (traceOf (perfectRoot refSponge MAP_TREE_DEPTH (depSpine.map (imtLeafHash refSponge)))
          depKey))
    ∧ (ReconcileGatesAt refSponge 2 (toyAbsentEnv refSponge) toyAbsentOp
      ∧ ¬ ReconcileGatesImtAt refSponge 2 (toyAbsentEnv refSponge) toyAbsentOp) := by
  refine ⟨⟨topGap_old_model_false, topGap_imt_model_holds⟩, toy_absent_gates refSponge, ?_⟩
  intro hg
  obtain ⟨c, lowAddr, lowValue, lowNext, -, hclen, hcroot, -⟩ := hg.1 rfl
  exact imtRoot_ne_mapRoot refSponge refSponge_CR 2 c toyHeap hclen rfl hcroot.symm

/-- **★ THE REPOINTED DENOTATION IS DELIVERED ON THAT ROW**, through the repointed arm rather than by
hand: `mapOpsArmImt_of_modeler` applied to the inhabited repointed premise. -/
theorem topGap_repointed_denotation_holds :
    MapOpImtHoldsAt refSponge
      (envAt (traceOf
        (perfectRoot refSponge MAP_TREE_DEPTH (depSpine.map (imtLeafHash refSponge))) depKey) 0)
      toyAbsentOp :=
  mapOpsArmImt_of_modeler refSponge refSponge_CR dTopGap
    (traceOf (perfectRoot refSponge MAP_TREE_DEPTH (depSpine.map (imtLeafHash refSponge))) depKey)
    topGap_imt_model_holds 0 (by rw [traceOf_rows_length]; omega) toyAbsentOp
    (List.mem_singleton_self _)

/-- **★ THE DELIVERABLE, IN ONE STATEMENT.** On ONE turn containing ONE fired top-gap `.absent` row,
at the DEPLOYED depth: the OLD apex premise is FALSE, the REPOINTED premise HOLDS, the repointed
denotation is DELIVERED — and the apex's own denotation `MapOp.holdsAt` is REFUTED, which is why the
apex conclusion does not follow from any premise here and the denotation is what must move. -/
theorem topGap_apex_premise_repointed :
    ¬ MapReconcileModelOk refSponge dTopGap
        (traceOf (perfectRoot refSponge MAP_TREE_DEPTH (depSpine.map (imtLeafHash refSponge)))
          depKey)
    ∧ MapReconcileImtModelOk refSponge dTopGap
        (traceOf (perfectRoot refSponge MAP_TREE_DEPTH (depSpine.map (imtLeafHash refSponge)))
          depKey)
    ∧ MapOpImtHoldsAt refSponge
        (envAt (traceOf
          (perfectRoot refSponge MAP_TREE_DEPTH (depSpine.map (imtLeafHash refSponge))) depKey) 0)
        toyAbsentOp
    ∧ ¬ MapOp.holdsAt refSponge
        (envAt (traceOf
          (perfectRoot refSponge MAP_TREE_DEPTH (depSpine.map (imtLeafHash refSponge))) depKey) 0)
        toyAbsentOp :=
  ⟨topGap_old_model_false, topGap_imt_model_holds, topGap_repointed_denotation_holds,
   topGap_mapOpHoldsAt_false⟩

/-- **The narrow toy top-gap witnesses, REUSED verbatim.** `MapAbsentImtGate.topGap_deployed_accepts`
(chain `topChain`, key `50`, low leaf `⟨40, 4, 100⟩`) IS a repointed `.absent` row body — the same
statement the deployed-depth exhibit above makes, on the epoch's own established witness, at its own
depth 2. -/
theorem toyTopGap_row_is_repointed (hash : List ℤ → ℤ) :
    ReconcileGatesImtAt hash 2 (rowOf (topRoot hash) 50) toyAbsentOp := by
  refine ⟨fun _ => ⟨topChain, 40, 4, 100, topChain_sorted, rfl, ?_, ?_⟩, fun hne => absurd rfl hne⟩
  · exact (rowOf_root _ _).trans rfl
  · rw [rowOf_root, rowOf_newRoot, rowOf_key]
    exact topGap_deployed_accepts hash


end Exhibit

/-! ## §5 — THE FINDING IN THE INSTRUMENT'S VOCABULARY (`PremiseInhabitability`), so it is
comparable with the FRI-side premise vacuity of `docs/WOUND-apex-premise-vacuity-2026-07-24.md`. -/

section Instrument

open Dregg2.Circuit.Poseidon2Binding.Reference (refSponge refSponge_CR)
open Dregg2.Circuit.PremiseInhabitability (AcceptsSome Empties not_of_empties_of_acceptsSome)

/-- The DEPLOYED-ROW acceptance predicate: traces carrying a fired declared map-op row whose
pre-root column is the indexed-Merkle commitment `heap_root.rs` actually computes. -/
def DeployedImtRow (hash : List ℤ → ℤ) (d : EffectVmDescriptor2) :
    Dregg2.Circuit.PremiseInhabitability.Acc VmTrace := fun t =>
  ∃ i, i < t.rows.length ∧ ∃ m ∈ mapOpsOf d, m.guard.eval (envAt t i).loc = 1 ∧
    ∃ c : List ImtLeaf, c.length = 2 ^ MAP_TREE_DEPTH ∧
      (m.root 0).eval (envAt t i).loc = perfectRoot hash MAP_TREE_DEPTH (c.map (imtLeafHash hash))

/-- **★ THE OLD PREMISE EMPTIES THE DEPLOYED ROWS.** Exactly the shape the FRI-side wound was caught
in: assuming the carried premise on every trace forces the deployed acceptance set to be EMPTY. -/
theorem oldModel_empties_deployedImtRows (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (d : EffectVmDescriptor2) :
    Empties (∀ t : VmTrace, MapReconcileModelOk hash d t) (DeployedImtRow hash d) := by
  intro hall t hrow
  obtain ⟨i, hi, m, hm, hguard, c, hc, heq⟩ := hrow
  exact mapReconcileModelOk_forbids_imtRootedRows hash hCR d t (hall t) i hi m hm hguard c hc heq

/-- The deployed acceptance set is INHABITED (the §4 exhibit). -/
theorem deployedImtRow_acceptsSome : AcceptsSome (DeployedImtRow refSponge dTopGap) := by
  refine ⟨traceOf (perfectRoot refSponge MAP_TREE_DEPTH (depSpine.map (imtLeafHash refSponge)))
      depKey, 0, ?_, toyAbsentOp, ?_, ?_, depSpine, depSpine_length, ?_⟩
  · rw [traceOf_rows_length]; omega
  · rw [dTopGap_mapOps]; exact List.mem_singleton_self _
  · rw [traceOf_loc]; exact rowOf_guard _ _
  · rw [traceOf_loc, rowOf_root]

/-- **★ HENCE THE OLD PREMISE IS FALSE, not merely uninformative** — the sharpest form, available
because the accepting pole is exhibited rather than assumed. -/
theorem old_model_is_false_on_deployed_rows :
    ¬ (∀ t : VmTrace, MapReconcileModelOk refSponge dTopGap t) :=
  not_of_empties_of_acceptsSome
    (oldModel_empties_deployedImtRows refSponge refSponge_CR dTopGap)
    deployedImtRow_acceptsSome

end Instrument

/-! ## §6 — AXIOM HYGIENE. -/

#assert_axioms imtRoot_ne_mapRoot
#assert_axioms opensToMerkle_unsat_at_imtRoot
#assert_axioms writesToMerkle_unsat_at_imtRoot
#assert_axioms reconcileGatesAt_unsat_at_imtRoot
#assert_axioms mapOpHoldsAt_unsat_at_imtRoot
#assert_axioms mapReconcileModelOk_forbids_imtRootedRows
#assert_axioms absentRowImt_force_imtOpensNone
#assert_axioms imtOpensNone_gives_projected_opening
#assert_axioms imtRootedRow_wire_does_not_reach_the_heap_slot
#assert_axioms mapOpsArmImt_of_modeler
#assert_axioms spineC_length
#assert_axioms spineC_add
#assert_axioms spineC_sorted
#assert_axioms spineC_addr_le
#assert_axioms spineC_open_last
#assert_axioms depGate_accepts
#assert_axioms topGap_old_model_false
#assert_axioms topGap_old_model_false_bracket
#assert_axioms topGap_imt_model_holds
#assert_axioms topGap_imt_absence_fires
#assert_axioms topGap_mapOpHoldsAt_false
#assert_axioms topGap_repointed_denotation_holds
#assert_axioms topGap_apex_premise_repointed
#assert_axioms models_are_incomparable
#assert_axioms toyTopGap_row_is_repointed
#assert_axioms oldModel_empties_deployedImtRows
#assert_axioms deployedImtRow_acceptsSome
#assert_axioms old_model_is_false_on_deployed_rows

end Dregg2.Circuit.MapReconcileImtRepoint

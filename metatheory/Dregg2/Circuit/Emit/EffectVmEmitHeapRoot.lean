/-
# Dregg2.Circuit.Emit.EffectVmEmitHeapRoot — the GENUINE in-row `heap_root` recompute
(REFINEMENT-DESIGN Decision 1; THE ROTATION's heap-write descriptor gadget).

THE HEAP generalizes the proven `cap_root` openable sorted-Poseidon2 machinery with a GENERIC leaf
(`Substrate.Heap`: `addr = hash[coll,key]`, `leaf = hash[addr,value]`, root = sponge of the sorted
leaf list). This module supplies the heap write's in-ROW recompute as a SHARED primitive built
DIRECTLY on the cap-root gate family (`EffectVmEmitCapRoot`): the SAME `VmHashSite` recompute shape,
the SAME `Poseidon2SpongeCR` anti-ghost, with the cap-edge leaf `hash[holder,target,rights,op]`
replaced by the heap two-site shape:

  1. **`siteHeapAddr`** — recompute the heap ADDRESS in-row: `addr = hash[ coll, key ]`. The prover
     cannot choose the address freely; it is `hash` of the bound `(collection_id, key)` (the design's
     "sorted-by-key-hash", `Substrate.Heap.addrOf`).
  2. **`siteHeapLeaf`** — recompute the heap LEAF in-row: `leaf = hash[ addr, value ]` (the
     generic-leaf generalization of the cap-edge leaf, `Substrate.Heap.leafOf`). Tampering the
     address OR the value moves the leaf.
  3. **`siteHeapRootAdvance`** — recompute the new `heap_root` in-row:
     `new_heap_root = hash[ leaf, old_heap_root ]` — the SAME prepend-accumulator advance the cap
     root uses (`EffectVmEmitCapRoot.siteCapRootAdvance`), reading the recomputed leaf and the OLD
     `heap_root` register column. The new root is FORCED by `(leaf, old_root)` — no free digest.

This is the cap-root Phase-A staging with a generic leaf: the per-touched-key membership-open /
leaf-update / sorted-insert is pinned-as-digest here (the prepend advance + its anti-ghost
`heapRoot_binds_write`); the genuine in-row sorted-TREE-update recompute (the bracketing
range-checks, mirroring the revocation circuit) reuses `Crypto.NonMembership.sorted_gap_excludes`
exactly as `Substrate.Heap.get_none_of_gap` already does — the Phase-E lane, out of scope here.

The new-root carrier is the `heap_root` register column (a non-`balance` state field absorbed into
`state_commit` by the same GROUP-4 mechanism `cap_root` uses), so tampering ANY of (coll, key,
value, old root, new root) provably moves `heap_root` ⇒ moves `state_commit` ⇒ UNSAT.

## cell≡circuit differential

The recomputed values read the SAME `Substrate.Heap` functions the cell stores and the executor
recomputes (`heapStepW_root_pinned`), so cell≡circuit is BY DEFINITION at this value layer (the
cap Phase-A discipline). The Rust differential mirroring `cap_root_cell_circuit_differential.rs` is
`circuit/tests/heap_root_cell_circuit_differential.rs`.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY as the named
`Poseidon2SpongeCR` hypothesis. Imports read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitCapRoot

namespace Dregg2.Circuit.Emit.EffectVmEmitHeapRoot

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.Emit.EffectVmEmitCapRoot (cN)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §0 — the param columns carrying the heap-write content `(collection_id, key, value)`.

Reuse the cap-edge param block (`EffectVmEmitCapRoot.cp`): the heap write's `(coll, key, value)`
ride the same param columns the cap edge `(holder, target, rights)` use — distinct effects, distinct
selectors, the SAME free param columns. -/
namespace hp
/-- The `collection_id` param column (cap-family `HOLDER` slot, reused). -/
def COLL  : Nat := EffectVmEmitCapRoot.cp.HOLDER
/-- The `key` param column (cap-family `TARGET` slot, reused). -/
def KEY   : Nat := EffectVmEmitCapRoot.cp.TARGET
/-- The written `value` param column (cap-family `RIGHTS` slot, reused). -/
def VALUE : Nat := EffectVmEmitCapRoot.cp.RIGHTS
end hp

/-! ## §1 — the in-row carriers for the recomputed address + leaf, and the old/new heap roots. -/

/-- The recomputed heap-ADDRESS carrier (`hash[coll,key]`). An aux column — the cap-edge-leaf
carrier slot, reused (this descriptor's selector ≠ a cap selector, so the slot never collides). -/
def HEAP_ADDR : Nat := EffectVmEmitCapRoot.CAP_EDGE_LEAF

/-- The recomputed heap-LEAF carrier (`hash[addr,value]`). The next aux slot past the address. -/
def HEAP_LEAF : Nat := EffectVmEmitCapRoot.CAP_EDGE_LEAF + 1

/-- The OLD `heap_root` carrier: the `state_before` `heap_root` register. We pin it to the same
state column the cap-root advance reads its old root from (`CAP_ROOT_BEFORE`) — the deployed layout
carries the `heap_root` register at this absorbed column for a heap-write row. -/
def HEAP_ROOT_BEFORE : Nat := EffectVmEmitCapRoot.CAP_ROOT_BEFORE

/-- The recomputed NEW `heap_root` carrier: the `state_after` register column GROUP-4 absorbs into
`state_commit` (the same absorbed carrier `cap_root` advances into). -/
def HEAP_ROOT_AFTER : Nat := EffectVmEmitCapRoot.CAP_ROOT_AFTER

/-! ## §2 — the THREE recompute hash-sites (genuine update — NOT opaque digests). -/

/-- **`siteHeapAddr`** — `addr = hash[ coll, key ]` (the sorted address; `Substrate.Heap.addrOf`). -/
def siteHeapAddr : VmHashSite :=
  { digestCol := HEAP_ADDR
  , inputs := [ .col (prmCol hp.COLL), .col (prmCol hp.KEY) ]
  , arity := 2 }

/-- **`siteHeapLeaf`** — `leaf = hash[ addr, value ]` (the generic leaf; `Substrate.Heap.leafOf`). -/
def siteHeapLeaf : VmHashSite :=
  { digestCol := HEAP_LEAF
  , inputs := [ .col HEAP_ADDR, .col (prmCol hp.VALUE) ]
  , arity := 2 }

/-- **`siteHeapRootAdvance`** — `new_heap_root = hash[ leaf, old_heap_root ]` (the prepend
accumulator advance, identical to the cap-root advance with the generic leaf). -/
def siteHeapRootAdvance : VmHashSite :=
  { digestCol := HEAP_ROOT_AFTER
  , inputs := [ .col HEAP_LEAF, .col HEAP_ROOT_BEFORE ]
  , arity := 2 }

/-- The three heap-root recompute sites, in order (address → leaf → advance). -/
def heapRecomputeSites : List VmHashSite := [ siteHeapAddr, siteHeapLeaf, siteHeapRootAdvance ]

/-! ## §2.D — the BASE heapWrite VM descriptor (the genuine in-row recompute as a registry effect).

The heap write's deployed circuit IS the three recompute sites: a row that satisfies it carries the
genuine `addr/leaf/new_root` chain (`heapRootHolds`), so the new `heap_root` register is FORCED to the
deterministic recompute of the bound `(coll, key, value, old_root)` — no free digest. `heapWriteVmDescriptor`
bundles them as a base `EffectVmDescriptor`: NO extra gate/range/PI (the recompute sites alone do the
forcing — the cap-root Phase-A discipline with a generic leaf). Rotated (`rotateV3`) + graduated
(`graduateV1`) it is `RotatedKernelRefinementExercise.heapWriteV3`, the LIVE registry member. The trace
width is `EFFECT_VM_WIDTH` (188 — the deployed effect-VM width; every recompute column the sites read
[`prmCol 0..2`, the cap-root carriers 65/87/102/103] lands `< 188`). -/

/-- **`heapWriteVmDescriptor`** — the base heapWrite circuit: its `hashSites` ARE the three heap-root
recompute sites (`heapRecomputeSites`), so a satisfying row's `siteHoldsAll` IS `heapRootHolds` — the
in-row recompute that FORCES the new `heap_root`. No extra constraints/ranges (the recompute is the whole
forcing content; the splice/guard/frame ride the decode residual in `heapWriteEncodes`). -/
def heapWriteVmDescriptor : EffectVmDescriptor :=
  { name        := "dregg-effectvm-heapWrite-v1"
  , traceWidth  := EFFECT_VM_WIDTH
  , piCount     := 0
  , constraints := []
  , hashSites   := heapRecomputeSites
  , ranges      := [] }

/-- The base heapWrite descriptor's `hashSites` ARE exactly the heap recompute sites (the bridge that
makes a satisfying row's `siteHoldsAll` equal `heapRootHolds`). -/
theorem heapWriteVmDescriptor_hashSites :
    heapWriteVmDescriptor.hashSites = heapRecomputeSites := rfl

/-! ## §2.E — the SPLICE base descriptor (PHASE-E: the genuine sorted-Merkle splice, MapOp-forced).

The accumulator advance (`siteHeapRootAdvance`, `new_root = hash[leaf, old_root]`) BINDS the new
`heap_root` to a deterministic function of the bound write content + old root, but it is NOT the
genuine sorted-Merkle SPLICE root `mapRoot (Heap.set h addr v)` (the binary-Merkle update over the
WHOLE sorted leaf list). The Phase-E close REPLACES the advance with a `.write` `MapOp` on the heap
root (`RotatedKernelRefinementExercise.heapSpliceWriteOp`): the deployed `Ir2Air::MapOps` AIR opens
the addressed OLD leaf against the committed `heap_root` (col 65) and FORCES the new `heap_root`
(col 87) to the genuine sorted-tree update — the binary-Merkle splice (`DescriptorIR2.writesTo`).

The advance site (col 87) and the splice `MapOp` (col 87) would JOINTLY pin the SAME column to two
DIFFERENT functions of the heap (`hash[leaf, oldRoot]` ≠ `mapRoot (set …)`), so the splice base
DROPS `siteHeapRootAdvance` and keeps ONLY the address+leaf sites: `siteHeapAddr` binds the MapOp's
KEY column (col 102 = `hash[coll, key]`) to the genuine sorted address; `siteHeapLeaf` binds the
leaf carrier (informational — the MapOps AIR recomputes the leaf internally). The new root is then
FORCED by the splice alone — the content-binding the advance could not give. -/

/-- The SPLICE recompute sites: address + leaf only (the advance is replaced by the splice `MapOp`).
`siteHeapAddr` binds the MapOp KEY (col 102 = `hash[coll, key]`); `siteHeapLeaf` binds the leaf
carrier. The new-root advance is DROPPED — it is forced by the `.write` `MapOp` (the genuine splice),
not the prepend accumulator. -/
def heapSpliceSites : List VmHashSite := [ siteHeapAddr, siteHeapLeaf ]

/-- **`heapWriteSpliceVmDescriptor`** — the SPLICE base heapWrite circuit: its `hashSites` are the
address+leaf sites only (NO advance). Rotated + graduated + appended with the splice `.write` `MapOp`
it is `RotatedKernelRefinementExercise.heapWriteV3` — the new root FORCED to the genuine sorted-Merkle
splice (`DescriptorIR2.writesTo`), not the prepend accumulator. -/
def heapWriteSpliceVmDescriptor : EffectVmDescriptor :=
  { name        := "dregg-effectvm-heapWrite-splice-v1"
  , traceWidth  := EFFECT_VM_WIDTH
  , piCount     := 0
  , constraints := []
  , hashSites   := heapSpliceSites
  , ranges      := [] }

/-- The splice base descriptor's `hashSites` ARE exactly the address+leaf sites. -/
theorem heapWriteSpliceVmDescriptor_hashSites :
    heapWriteSpliceVmDescriptor.hashSites = heapSpliceSites := rfl

/-! ## §3 — the recomputed values as pure functions (what the sites FORCE). -/

/-- The address as a function of `(coll, key)` (the unique `hash` image the address site forces). -/
def addrOf (hash : List ℤ → ℤ) (coll key : ℤ) : ℤ := hash [ coll, key ]

/-- The leaf as a function of `(addr, value)` (the unique `hash` image the leaf site forces). -/
def leafOf (hash : List ℤ → ℤ) (addr value : ℤ) : ℤ := hash [ addr, value ]

/-- The advanced `heap_root` as a function of `(leaf, old_root)`. NO free digest survives. -/
def heapAdvanceOf (hash : List ℤ → ℤ) (leaf oldRoot : ℤ) : ℤ := hash [ leaf, oldRoot ]

/-! ## §4 — `heapRootHolds`: the three recompute sites hold on `env`. -/

def heapRootHolds (hash : List ℤ → ℤ) (env : VmRowEnv) : Prop :=
  siteHoldsAll hash env heapRecomputeSites

/-- **`heapAddr_forced`** — the address carrier IS `hash[coll,key]`. -/
theorem heapAddr_forced (hash : List ℤ → ℤ) (env : VmRowEnv) (h : heapRootHolds hash env) :
    env.loc HEAP_ADDR = addrOf hash (env.loc (prmCol hp.COLL)) (env.loc (prmCol hp.KEY)) := by
  unfold heapRootHolds heapRecomputeSites siteHoldsAll at h
  simp only [siteHoldsAll.go, siteHeapAddr, siteHeapLeaf, siteHeapRootAdvance,
    VmHashSite.resolvedInputs, HashInput.resolve, List.map_cons, List.map_nil] at h
  obtain ⟨h0, _⟩ := h
  rw [h0]; rfl

/-- **`heapLeaf_forced`** — the leaf carrier IS `hash[addr,value]` where `addr` is itself the
recomputed `hash[coll,key]`. -/
theorem heapLeaf_forced (hash : List ℤ → ℤ) (env : VmRowEnv) (h : heapRootHolds hash env) :
    env.loc HEAP_LEAF
      = leafOf hash (addrOf hash (env.loc (prmCol hp.COLL)) (env.loc (prmCol hp.KEY)))
          (env.loc (prmCol hp.VALUE)) := by
  have haddr := heapAddr_forced hash env h
  unfold heapRootHolds heapRecomputeSites siteHoldsAll at h
  simp only [siteHoldsAll.go, siteHeapAddr, siteHeapLeaf, siteHeapRootAdvance,
    VmHashSite.resolvedInputs, HashInput.resolve, List.map_cons, List.map_nil] at h
  obtain ⟨_, h1, _⟩ := h
  rw [h1, haddr]; rfl

/-- **`heapRootAdvance_forced`** — the NEW `heap_root` carrier IS
`hash[ hash[addr,value], old_root ]` where `addr = hash[coll,key]`: a DETERMINISTIC FUNCTION of (the
bound `(coll, key, value)`, the old root). The genuine recompute — NO opaque digest param. -/
theorem heapRootAdvance_forced (hash : List ℤ → ℤ) (env : VmRowEnv) (h : heapRootHolds hash env) :
    env.loc HEAP_ROOT_AFTER
      = heapAdvanceOf hash
          (leafOf hash (addrOf hash (env.loc (prmCol hp.COLL)) (env.loc (prmCol hp.KEY)))
            (env.loc (prmCol hp.VALUE)))
          (env.loc HEAP_ROOT_BEFORE) := by
  have hleaf := heapLeaf_forced hash env h
  unfold heapRootHolds heapRecomputeSites siteHoldsAll at h
  simp only [siteHoldsAll.go, siteHeapAddr, siteHeapLeaf, siteHeapRootAdvance,
    VmHashSite.resolvedInputs, HashInput.resolve, List.map_cons, List.map_nil] at h
  obtain ⟨_, _, h2, _⟩ := h
  rw [h2, hleaf]; rfl

/-- **`heapSplice_addr_forced`** — the address carrier IS `hash[coll,key]` from the SPLICE sites (the
MapOp KEY binding): a satisfying splice row binds col 102 to the genuine sorted address, so the
`.write` MapOp's key is the real `hash[coll,key]`, not a free column. -/
theorem heapSplice_addr_forced (hash : List ℤ → ℤ) (env : VmRowEnv)
    (h : siteHoldsAll hash env heapSpliceSites) :
    env.loc HEAP_ADDR = addrOf hash (env.loc (prmCol hp.COLL)) (env.loc (prmCol hp.KEY)) := by
  unfold heapSpliceSites siteHoldsAll at h
  simp only [siteHoldsAll.go, siteHeapAddr, siteHeapLeaf,
    VmHashSite.resolvedInputs, HashInput.resolve, List.map_cons, List.map_nil] at h
  obtain ⟨h0, _⟩ := h
  rw [h0]; rfl

/-! ## §5 — THE ANTI-GHOST: the recomputed root BINDS the write content + old root. -/

/-- **`heapRoot_binds_write` — THE genuine-recompute anti-ghost.** Two recompute-honest rows with
EQUAL new `heap_root` carriers share the old root AND the bound `(coll, key, value)`. Off
`Poseidon2SpongeCR`: peel the advance hash (`[leaf, old]` equal), then the leaf hash (`[addr, value]`
equal), then the address hash (`[coll, key]` equal). Tampering ANY of them moves the new root —
the `capRoot_binds_edge` tooth with the generic-leaf two-site shape. -/
theorem heapRoot_binds_write (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (h₁ : heapRootHolds hash e₁) (h₂ : heapRootHolds hash e₂)
    (hroot : e₁.loc HEAP_ROOT_AFTER = e₂.loc HEAP_ROOT_AFTER) :
    e₁.loc HEAP_ROOT_BEFORE = e₂.loc HEAP_ROOT_BEFORE
    ∧ e₁.loc (prmCol hp.COLL) = e₂.loc (prmCol hp.COLL)
    ∧ e₁.loc (prmCol hp.KEY) = e₂.loc (prmCol hp.KEY)
    ∧ e₁.loc (prmCol hp.VALUE) = e₂.loc (prmCol hp.VALUE) := by
  rw [heapRootAdvance_forced hash e₁ h₁, heapRootAdvance_forced hash e₂ h₂] at hroot
  unfold heapAdvanceOf leafOf addrOf at hroot
  -- outer advance: hash [leaf₁, old₁] = hash [leaf₂, old₂]
  have houter := hCR _ _ hroot
  rw [List.cons.injEq, List.cons.injEq] at houter
  obtain ⟨hleafEq, hold, _⟩ := houter
  -- inner leaf: hash [addr₁, value₁] = hash [addr₂, value₂]
  have hleaf := hCR _ _ hleafEq
  rw [List.cons.injEq, List.cons.injEq] at hleaf
  obtain ⟨haddrEq, hval, _⟩ := hleaf
  -- innermost address: hash [coll₁, key₁] = hash [coll₂, key₂]
  have haddr := hCR _ _ haddrEq
  rw [List.cons.injEq, List.cons.injEq] at haddr
  obtain ⟨hc, hk, _⟩ := haddr
  exact ⟨hold, hc, hk, hval⟩

/-- **`heapRoot_value_bound` — the load-bearing corollary.** Two recompute-honest rows with the same
new `heap_root` wrote the SAME value at the same `(coll, key)` — the root pins WHAT was written, not
just that something was. -/
theorem heapRoot_value_bound (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (h₁ : heapRootHolds hash e₁) (h₂ : heapRootHolds hash e₂)
    (hroot : e₁.loc HEAP_ROOT_AFTER = e₂.loc HEAP_ROOT_AFTER) :
    e₁.loc (prmCol hp.VALUE) = e₂.loc (prmCol hp.VALUE) :=
  (heapRoot_binds_write hash hCR e₁ e₂ h₁ h₂ hroot).2.2.2

/-! ## §6 — NON-VACUITY: a concrete recompute fires; a tampered write moves the root. -/

/-- A concrete heap-write row: coll=3 (col 70), key=4 (col 71), value=42 (col 72),
old_heap_root=1000 (col 65). The address/leaf/new-root carriers (cols 102/103/87) hold the genuine
recomputed values under the toy sponge `cN`, so the recompute holds. -/
def goodHeapRow : VmRowEnv where
  loc := fun v =>
    if v = 70 then 3
    else if v = 71 then 4
    else if v = 72 then 42
    else if v = 65 then 1000
    else if v = 102 then cN [3, 4]
    else if v = 103 then cN [cN [3, 4], 42]
    else if v = 87 then cN [cN [cN [3, 4], 42], 1000]
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

-- The witness row's literal columns ARE the symbolic carrier columns (anti-drift).
#guard prmCol hp.COLL == 70
#guard prmCol hp.KEY == 71
#guard prmCol hp.VALUE == 72
#guard HEAP_ROOT_BEFORE == 65
#guard HEAP_ADDR == 102
#guard HEAP_LEAF == 103
#guard HEAP_ROOT_AFTER == 87

/-- **NON-VACUITY (witness TRUE).** `goodHeapRow` satisfies the recompute under the concrete sponge
— the three sites carry their genuine digests. The recompute predicate is INHABITED. -/
theorem goodHeapRow_recomputes : heapRootHolds cN goodHeapRow := by
  have hC : prmCol hp.COLL = 70 := by decide
  have hK : prmCol hp.KEY = 71 := by decide
  have hV : prmCol hp.VALUE = 72 := by decide
  have hB : HEAP_ROOT_BEFORE = 65 := by decide
  have hA : HEAP_ADDR = 102 := by decide
  have hL : HEAP_LEAF = 103 := by decide
  have hF : HEAP_ROOT_AFTER = 87 := by decide
  unfold heapRootHolds heapRecomputeSites siteHoldsAll
  simp only [siteHoldsAll.go, siteHeapAddr, siteHeapLeaf, siteHeapRootAdvance,
    VmHashSite.resolvedInputs, HashInput.resolve, List.map_cons, List.map_nil,
    hC, hK, hV, hB, hA, hL, hF]
  refine ⟨?_, ?_, ?_, trivial⟩
  · show goodHeapRow.loc 102 = cN [goodHeapRow.loc 70, goodHeapRow.loc 71]; decide
  · show goodHeapRow.loc 103 = cN [goodHeapRow.loc 102, goodHeapRow.loc 72]; decide
  · show goodHeapRow.loc 87 = cN [goodHeapRow.loc 103, goodHeapRow.loc 65]; decide

/-- **NON-VACUITY (witness FALSE / anti-ghost on value).** Writing a DIFFERENT value (42 → 99) at the
same `(coll, key)` and old root yields a DIFFERENT new root — the value is bound. -/
theorem tampered_value_moves_root :
    heapAdvanceOf cN (leafOf cN (addrOf cN 3 4) 42) 1000
      ≠ heapAdvanceOf cN (leafOf cN (addrOf cN 3 4) 99) 1000 := by
  unfold heapAdvanceOf leafOf addrOf cN
  norm_num

/-- **NON-VACUITY (witness FALSE / anti-ghost on address).** Writing the same value at a DIFFERENT
`(coll, key)` (3,4 → 5,6) yields a DIFFERENT new root — the address is bound. -/
theorem tampered_addr_moves_root :
    heapAdvanceOf cN (leafOf cN (addrOf cN 3 4) 42) 1000
      ≠ heapAdvanceOf cN (leafOf cN (addrOf cN 5 6) 42) 1000 := by
  unfold heapAdvanceOf leafOf addrOf cN
  norm_num

/-! ## §7 — Axiom-hygiene + layout pins. -/

-- The new-root carrier IS the absorbed `heap_root` (= cap-root) state-after column.
#guard HEAP_ROOT_AFTER == EffectVmEmitCapRoot.CAP_ROOT_AFTER
#guard HEAP_ROOT_BEFORE == EffectVmEmitCapRoot.CAP_ROOT_BEFORE
-- The address / leaf / before / after carriers are DISTINCT.
#guard [HEAP_ADDR, HEAP_LEAF, HEAP_ROOT_BEFORE, HEAP_ROOT_AFTER].dedup.length == 4
-- The write param columns are distinct + in-range.
#guard [hp.COLL, hp.KEY, hp.VALUE].dedup.length == 3
#guard [hp.COLL, hp.KEY, hp.VALUE].all (· < NUM_PARAMS)
-- The recompute is three ordered sites (address, leaf, advance).
#guard heapRecomputeSites.length == 3

#assert_axioms heapAddr_forced
#assert_axioms heapLeaf_forced
#assert_axioms heapRootAdvance_forced
#assert_axioms heapRoot_binds_write
#assert_axioms heapRoot_value_bound
#assert_axioms goodHeapRow_recomputes
#assert_axioms tampered_value_moves_root
#assert_axioms tampered_addr_moves_root
#assert_axioms heapSplice_addr_forced

end Dregg2.Circuit.Emit.EffectVmEmitHeapRoot

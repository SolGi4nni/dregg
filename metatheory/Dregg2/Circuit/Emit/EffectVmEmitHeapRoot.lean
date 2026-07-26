/-
# Dregg2.Circuit.Emit.EffectVmEmitHeapRoot — the GENUINE sorted-Merkle heap-write descriptor
(REFINEMENT-DESIGN Decision 1; THE ROTATION's heap-write descriptor gadget).

THE HEAP generalizes the proven `cap_root` openable sorted-Poseidon2 machinery with a GENERIC leaf
(`Substrate.Heap`: `addr = hash[coll,key]`, root = a depth-16 binary-Merkle fold of the sorted leaf
list). This module supplies the heap write's in-ROW address recompute and the SPLICE base descriptor.

## ⚠ SAY THE SUBSTRATE, AND SAY WHICH LEAF (read this before quoting anything below)

This is Lean-authored AIR: `heapWriteSpliceVmDescriptor` is the byte source of a DEPLOYED descriptor
(`heapWriteVmDescriptor2R24` — narrow at `circuit/descriptors/rotation-v3-staged-registry.tsv:47`,
WIDE at `rotation-wide-registry-staged.tsv`, and the wide member is RESOLVED BY THE LIVE VERIFIER,
`turn/src/executor/proof_verify.rs` `LIVE_ONLY_BARE_KEYS`). So the shapes named here are not model
prose; they are emitted constraints a prover runs.

★ **THE DEPLOYED HEAP LEAF IS ARITY-3, AND IT IS NOT `siteHeapLeaf`.** On 2026-07-12 (`919b2b0b8d`)
`heap_root.rs` became an INDEXED Merkle tree: the leaf is `hash[addr, value, next_addr]`
(`HeapLeaf::preimage`, `HEAP_LEAF_ARITY = 3`, the single place the schema is written since
`b2da6d431`) and the stored MAX-sentinel leaf was retired to a terminal pointer
(`HEAP_SENTINEL_LEAVES = 1`). The leaf that ACTUALLY authenticates against the committed root in this
descriptor is that arity-3 IMT leaf, at NATIVE 8-felt width, in the heap-open READ appendix and the
after-spine — `Emit.HeapOpenEmit.heapLeafInputs` (arity 3, `#guard`-pinned) / `heapLeafDigest_sound8`
/ `afterSpineColsH`, realized by `fill_heap_open_read` / `fill_heap_after_spine`. That leg is
CORRECT and was moved with the tree.

`siteHeapLeaf` (§2) is what was NOT moved: a 1-felt ARITY-2 `hash[addr, value]` recompute that is
still EMITTED into the deployed bytes and is no longer any leaf of any deployed tree. It is a
VESTIGE — §8 proves the separation and pins that nothing in this descriptor reads it. Do not quote
`heapSplice_leaf_forced` (§4) as "the heap leaf is forced"; it forces a retired digest.
The new `heap_root` is FORCED — not by a prepend accumulator — but by a genuine `.write` `MapOp` whose
`Ir2Air::MapOps` AIR opens the addressed OLD leaf against the committed root and recomputes the sorted-tree
update (see `RotatedKernelRefinementExercise.heapWriteV3` + `DescriptorIR2.writesTo`).

Two in-row recompute sites (the cap-root gate family reused, `EffectVmEmitCapRoot`; the SAME `VmHashSite`
shape, the cap-edge leaf `hash[holder,target,rights,op]` replaced by the heap two-site shape):

  1. **`siteHeapAddr`** — recompute the heap ADDRESS in-row: `addr = hash[ coll, key ]`. The prover
     cannot choose the address freely; it is `hash` of the bound `(collection_id, key)` (the design's
     "sorted-by-key-hash", `Substrate.Heap.addrOf`). This binds the splice `MapOp`'s KEY column.
  2. **`siteHeapLeaf`** — ⚠ THE VESTIGE. Recomputes `hash[ addr, value ]` in-row (arity 2,
     `Substrate.Heap.leafOf`). This WAS the heap leaf before the 2026-07-12 IMT move; it is not the
     deployed leaf now (that is arity-3, see the banner) and nothing in this descriptor reads the
     column. Retained because it is in the CHECKED-IN BYTES; §8 carries the separation, the
     unread-ness pin, and the post-flag-day site list that drops it.

## Where the new root is FORCED (the SPLICE, NOT a prepend digest)

The new `heap_root` is NOT advanced by a prepend accumulator `hash[leaf, old_root]` — that digest is a
function of `(leaf, old_root)` a prover can pick without performing the real sorted-tree insert. Instead
`heapWriteSpliceVmDescriptor` (§2.E) carries ONLY the address+leaf sites and delegates the new-root
forcing to a `.write` `MapOp` (`RotatedKernelRefinementExercise.heapSpliceWriteOp`), appended when the
descriptor is rotated + graduated into `heapWriteV3`. The deployed `Ir2Air::MapOps` AIR
(`DescriptorIR2.MapOp.holdsAt .write`, denotation `DescriptorIR2.writesTo`) forces the new root to the
genuine sorted insert-or-update over the WHOLE leaf list, opened against the committed old root
(`heap_root.rs::CanonicalHeapTree::update_witness`); a content-mismatched root has no witness.

⚠ **NOT `mapRoot (Heap.set h addr value)`, which this header used to claim.** `mapRoot` is the ARITY-2
`Heap.leafOf` binary fold, and under the CR floor an arity-3 IMT root is NEVER an arity-2 `mapRoot`
(`MapReconcileImtRepoint.imtRoot_ne_mapRoot`, lifting `MapAbsentImtGate.imtLeafHash_ne_heapLeafOf`).
So the `SAT ⟹ mapRoot (Heap.set …)` theorem
(`RotatedKernelRefinementExercise.heapWrite_realizes_heapSet`) and the forged-root rejections
(`heapWrite_sat_rejects_forged_root` / `heapWrite_sat_rejects_wrong_splice_root`) are theorems about
the RETIRED arity-2 commitment, not about the tree the prover folds — the same class of wound as the
`.absent` arm. The Lean denotation cutover is `docs/DESIGN-mapop-denotation-move.md`; the landed
DEPLOYED-shape denotation is `MapPaddedDenotation.padImtSchema` / `padImtTeeth` (arity-3 IMT leaves,
deployed relink, zero padding) with the four arm laws in `MapKindImtGates`. The deployed-level
splice-present tooth that does NOT go through `mapRoot` is
`circuit/tests/heap_write_deployed_root_forced.rs`.

The new-root carrier is the `heap_root` register column (a non-`balance` state field absorbed into
`state_commit` by the same GROUP-4 mechanism `cap_root` uses); the splice reads/writes it via the
ROTATED limbs (`HEAP_ROOT_BEFORE_ROT` / `HEAP_ROOT_AFTER_ROT` in `RotatedKernelRefinementExercise`).

## cell≡circuit differential

The recomputed ADDRESS reads the SAME `Substrate.Heap.addrOf` the cell stores and the executor
recomputes, so cell≡circuit is BY DEFINITION at that value layer (the cap Phase-A discipline). ⚠ The
LEAF leg of that claim no longer holds through `siteHeapLeaf`: the cell's committed leaf is the arity-3
IMT leaf, so cell≡circuit at the leaf layer runs through the heap-open appendix (`HeapOpenEmit`), not
through §2's site. The Rust differential is `circuit/tests/heap_root_cell_circuit_differential.rs`
(whose `reference_root` was re-derived at the arity-3 shape in `b2da6d431`) /
`circuit/tests/heap_write_deployed_root_forced.rs` (the deployed-level splice-present + root-forced tripwire).

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY as the named
`Poseidon2SpongeCR` hypothesis where used downstream. Imports read-only.
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
carrier slot, reused (this descriptor's selector ≠ a cap selector, so the slot never collides).
This is the column the splice `.write` `MapOp` reads as its KEY. -/
def HEAP_ADDR : Nat := EffectVmEmitCapRoot.CAP_EDGE_LEAF

/-- The recomputed heap-LEAF carrier (`hash[addr,value]`). The next aux slot past the address. -/
def HEAP_LEAF : Nat := EffectVmEmitCapRoot.CAP_EDGE_LEAF + 1

/-- The OLD `heap_root` carrier: the `state_before` `heap_root` register (the absorbed cap-root
before column `CAP_ROOT_BEFORE`). The deployed layout carries the `heap_root` register at this
absorbed column for a heap-write row. The splice `MapOp` reads the committed root off the ROTATED
limb (`HEAP_ROOT_BEFORE_ROT`); this constant pins the v1-state carrier. -/
def HEAP_ROOT_BEFORE : Nat := EffectVmEmitCapRoot.CAP_ROOT_BEFORE

/-- The NEW `heap_root` carrier: the `state_after` register column GROUP-4 absorbs into
`state_commit` (the same absorbed carrier `cap_root` advances into). The splice `MapOp` forces the
new root off the ROTATED limb (`HEAP_ROOT_AFTER_ROT`); this constant pins the v1-state carrier. -/
def HEAP_ROOT_AFTER : Nat := EffectVmEmitCapRoot.CAP_ROOT_AFTER

/-! ## §2 — the TWO in-row recompute hash-sites (address + leaf; the new root is splice-forced). -/

/-- **`siteHeapAddr`** — `addr = hash[ coll, key ]` (the sorted address; `Substrate.Heap.addrOf`). -/
def siteHeapAddr : VmHashSite :=
  { digestCol := HEAP_ADDR
  , inputs := [ .col (prmCol hp.COLL), .col (prmCol hp.KEY) ]
  , arity := 2 }

/-- **`siteHeapLeaf`** — ⚠ **THE VESTIGE**, arity 2: `hash[ addr, value ]`
(`Substrate.Heap.leafOf`). NOT the deployed heap leaf, which is the arity-3 IMT leaf
`hash[addr, value, next_addr]` (`heap_root.rs::HeapLeaf::preimage`, `Emit.HeapOpenEmit.heapLeafInputs`)
— see §8 for the machine-checked separation, the pin that no site in this descriptor reads
`HEAP_LEAF`, and the post-flag-day site list. Still emitted because it is in the checked-in bytes. -/
def siteHeapLeaf : VmHashSite :=
  { digestCol := HEAP_LEAF
  , inputs := [ .col HEAP_ADDR, .col (prmCol hp.VALUE) ]
  , arity := 2 }

/-! ## §2.E — THE heapWrite VM descriptor (PHASE-E: the genuine sorted-Merkle splice, MapOp-forced).

The new `heap_root` is FORCED by the genuine sorted-Merkle SPLICE over the WHOLE sorted leaf list, NOT
a prepend accumulator advance. The `.write` `MapOp` on the heap root
(`RotatedKernelRefinementExercise.heapSpliceWriteOp`) is realized by the deployed `Ir2Air::MapOps` AIR:
it opens the addressed OLD leaf against the committed `heap_root` (the rotated limb) and FORCES the new
`heap_root` to the genuine sorted-tree update. ⚠ The Lean denotation of that arm
(`DescriptorIR2.writesTo`) still commits ARITY-2 `Heap.leafOf` leaves; the deployed-shape denotation is
`MapPaddedDenotation.padImtSchema` (see the banner).

The base descriptor carries the address site and the vestigial leaf site: `siteHeapAddr` binds the
MapOp's KEY column (`HEAP_ADDR = hash[coll, key]`) to the genuine sorted address — that is the
load-bearing one. `siteHeapLeaf` binds nothing the MapOp or the heap-open appendix reads (§8's
`heapSpliceSites_never_read_HEAP_LEAF`); the MapOps AIR recomputes the ARITY-3 leaf internally along the
opened path. The new root is FORCED by the splice alone — the content-binding a prepend digest could not
give. -/

/-- The heapWrite recompute sites: the address site + the vestigial leaf site (the new-root advance is
the splice `MapOp`). `siteHeapAddr` binds the MapOp KEY (`HEAP_ADDR = hash[coll, key]`); `siteHeapLeaf`
is the retired arity-2 leaf (§8). **These are the CHECKED-IN BYTES** — see §8 for
`heapSpliceSitesImt`, the shape after the ember-gated regen. -/
def heapSpliceSites : List VmHashSite := [ siteHeapAddr, siteHeapLeaf ]

/-- **`heapWriteSpliceVmDescriptor`** — THE base heapWrite circuit (NO prepend advance). Rotated +
graduated + appended with the splice `.write` `MapOp` it is
`RotatedKernelRefinementExercise.heapWriteV3`, whose emitted bytes are the DEPLOYED
`heapWriteVmDescriptor2R24`. The trace width is `EFFECT_VM_WIDTH` (the deployed effect-VM width; every
recompute column the sites read lands `< width`). -/
def heapWriteSpliceVmDescriptor : EffectVmDescriptor :=
  { name        := "dregg-effectvm-heapWrite-splice-v1"
  , traceWidth  := EFFECT_VM_WIDTH
  , piCount     := 0
  , constraints := []
  , hashSites   := heapSpliceSites
  , ranges      := [] }

/-- The heapWrite base descriptor's `hashSites` ARE exactly the address+leaf sites. -/
theorem heapWriteSpliceVmDescriptor_hashSites :
    heapWriteSpliceVmDescriptor.hashSites = heapSpliceSites := rfl

/-! ## §3 — the recomputed values as pure functions (what the address/leaf sites FORCE). -/

/-- The address as a function of `(coll, key)` (the unique `hash` image the address site forces). -/
def addrOf (hash : List ℤ → ℤ) (coll key : ℤ) : ℤ := hash [ coll, key ]

/-- The RETIRED arity-2 leaf as a function of `(addr, value)` (the unique `hash` image the vestigial
leaf site forces). ⚠ Not the deployed leaf — see `deployedImtLeafOf` in §8. -/
def leafOf (hash : List ℤ → ℤ) (addr value : ℤ) : ℤ := hash [ addr, value ]

/-! ## §4 — the address + leaf carriers are FORCED by a satisfying splice row. -/

/-- **`heapSplice_addr_forced`** — the address carrier IS `hash[coll,key]` from the splice sites (the
MapOp KEY binding): a satisfying splice row binds `HEAP_ADDR` to the genuine sorted address, so the
`.write` MapOp's key is the real `hash[coll,key]`, not a free column. -/
theorem heapSplice_addr_forced (hash : List ℤ → ℤ) (env : VmRowEnv)
    (h : siteHoldsAll hash env heapSpliceSites) :
    env.loc HEAP_ADDR = addrOf hash (env.loc (prmCol hp.COLL)) (env.loc (prmCol hp.KEY)) := by
  unfold heapSpliceSites siteHoldsAll at h
  simp only [siteHoldsAll.go, siteHeapAddr, siteHeapLeaf,
    VmHashSite.resolvedInputs, HashInput.resolve, List.map_cons, List.map_nil] at h
  obtain ⟨h0, _⟩ := h
  rw [h0]; rfl

/-- **`heapSplice_leaf_forced`** — ⚠ **SCOPE: this forces a RETIRED digest.** The `HEAP_LEAF` carrier IS
`hash[addr,value]` (arity 2) from the splice sites, where `addr` is the recomputed address carrier. TRUE
about the emitted bytes, and that is all it says: `hash[addr,value]` is not any leaf of the deployed
arity-3 IMT (§8 `siteHeapLeaf_is_not_the_deployed_leaf`), and no constraint in this descriptor reads
`HEAP_LEAF` (§8 `heapSpliceSites_never_read_HEAP_LEAF`). Do NOT cite this as "the heap leaf is forced" —
the deployed leaf binding is `HeapOpenEmit.heapLeafDigest_sound8` (arity 3, native 8 felts). -/
theorem heapSplice_leaf_forced (hash : List ℤ → ℤ) (env : VmRowEnv)
    (h : siteHoldsAll hash env heapSpliceSites) :
    env.loc HEAP_LEAF = leafOf hash (env.loc HEAP_ADDR) (env.loc (prmCol hp.VALUE)) := by
  unfold heapSpliceSites siteHoldsAll at h
  simp only [siteHoldsAll.go, siteHeapAddr, siteHeapLeaf,
    VmHashSite.resolvedInputs, HashInput.resolve, List.map_cons, List.map_nil] at h
  obtain ⟨_, h1, _⟩ := h
  rw [h1]; rfl

/-! ## §5 — THE ANTI-GHOST lives with the splice.

The Lean new-root anti-ghost is `DescriptorIR2.writesTo_functional` (under `Poseidon2SpongeCR`, via
`MapMerkleRoot.mapRoot_injective`): a satisfying `heapWriteV3` row's new `heap_root` is the UNIQUE
sorted-Merkle splice of the committed heap content — a prover cannot keep the published root while
tampering the address or value. ⚠ **AT THE ARITY-2 COMMITMENT.** `mapRoot_injective` is injectivity of
the retired arity-2 fold, so this anti-ghost — and the end-to-end
`RotatedKernelRefinementExercise.heapWrite_realizes_heapSet` / `heapWrite_sat_rejects_forged_root` — are
about a commitment the prover does not fold. The DEPLOYED-shape anti-ghost that composes here is
`MapPaddedDenotation.padImtRoot_binds_or_ghost_or_collides` / `writesToMerkleS_functional_of_good` at
`padImtTeeth sent`, whose non-vacuity already bites at `MAP_TREE_DEPTH = 16` over a SPARSE tree
(`bite_presents` / `bite_absence_is_refused` / `bite_write_is_functional`) — compose it, do not
re-derive it.

The ADDRESS carrier is in-row bound (`heapSplice_addr_forced`), so the splice is keyed by the real
`hash[coll,key]`; the `HEAP_LEAF` carrier binding (`heapSplice_leaf_forced`) contributes NOTHING to the
splice (§8). -/

/-! ## §6 — NON-VACUITY: a concrete splice row fires; a tampered write moves the leaf. -/

/-- A concrete heap-write splice row: coll=3 (col 70), key=4 (col 71), value=42 (col 72). The
address/leaf carriers (cols 102/103) hold the genuine recomputed values under the toy sponge `cN`, so
the splice recompute holds. -/
def goodSpliceRow : VmRowEnv where
  loc := fun v =>
    if v = 70 then 3
    else if v = 71 then 4
    else if v = 72 then 42
    else if v = 102 then cN [3, 4]
    else if v = 103 then cN [cN [3, 4], 42]
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

-- The witness row's literal columns ARE the symbolic carrier columns (anti-drift).
#guard prmCol hp.COLL == 70
#guard prmCol hp.KEY == 71
#guard prmCol hp.VALUE == 72
#guard HEAP_ADDR == 102
#guard HEAP_LEAF == 103

/-- **NON-VACUITY (witness TRUE).** `goodSpliceRow` satisfies the address+leaf recompute under the
concrete sponge — the two sites carry their genuine digests. The recompute predicate is INHABITED. -/
theorem goodSpliceRow_recomputes : siteHoldsAll cN goodSpliceRow heapSpliceSites := by
  have hC : prmCol hp.COLL = 70 := by decide
  have hK : prmCol hp.KEY = 71 := by decide
  have hV : prmCol hp.VALUE = 72 := by decide
  have hA : HEAP_ADDR = 102 := by decide
  have hL : HEAP_LEAF = 103 := by decide
  unfold heapSpliceSites siteHoldsAll
  simp only [siteHoldsAll.go, siteHeapAddr, siteHeapLeaf,
    VmHashSite.resolvedInputs, HashInput.resolve, List.map_cons, List.map_nil,
    hC, hK, hV, hA, hL]
  refine ⟨?_, ?_, trivial⟩
  · show goodSpliceRow.loc 102 = cN [goodSpliceRow.loc 70, goodSpliceRow.loc 71]; decide
  · show goodSpliceRow.loc 103 = cN [goodSpliceRow.loc 102, goodSpliceRow.loc 72]; decide

/-- **NON-VACUITY (anti-ghost on value).** Writing a DIFFERENT value (42 → 99) at the same `(coll, key)`
yields a DIFFERENT leaf — the value is bound (and the leaf feeds the sorted-Merkle splice). -/
theorem tampered_value_moves_leaf :
    leafOf cN (addrOf cN 3 4) 42 ≠ leafOf cN (addrOf cN 3 4) 99 := by
  unfold leafOf addrOf cN
  norm_num

/-- **NON-VACUITY (anti-ghost on address).** Writing the same value at a DIFFERENT `(coll, key)`
(3,4 → 5,6) yields a DIFFERENT leaf — the address is bound. -/
theorem tampered_addr_moves_leaf :
    leafOf cN (addrOf cN 3 4) 42 ≠ leafOf cN (addrOf cN 5 6) 42 := by
  unfold leafOf addrOf cN
  norm_num

/-! ## §8 — ⚑ THE VESTIGE, MEASURED: `siteHeapLeaf` COMMITS A RETIRED LEAF SHAPE.

This section exists because the site is on the EMIT side. `heapWriteSpliceVmDescriptor` is the byte
source of a descriptor the deployed light client resolves, so "the Lean names the wrong object" here is
one step from "the descriptor models the wrong object". What follows establishes, machine-checked, which
of those two it is — and the answer is the first, not the second:

  (1) `siteHeapLeaf` absorbs a preimage the deployed leaf does NOT have (`siteHeapLeaf_arity`,
      `siteHeapLeaf_preimage_ne_deployed`) and its digest genuinely differs at a NAMED sponge and a
      NAMED witness (`siteHeapLeaf_is_not_the_deployed_leaf`) — no floor, no existential.
  (2) NO site in this descriptor reads `HEAP_LEAF` (`heapSpliceSites_never_read_HEAP_LEAF`, decided
      over the emitted input lists). The splice `MapOp`'s key is `HEAP_ADDR` and its value is
      `prmCol hp.VALUE` — the deployed bytes confirm it (`heap_write_deployed_root_forced.rs`
      `deployed_heapwrite_forces_sorted_merkle_splice` asserts `m.key = Var(HEAP_ADDR)` /
      `m.value = Var(VALUE)`). ★ MEASURED ACROSS THE WHOLE COMMITTED CONSTRAINT LIST, not just the
      hash layer: decoding both registry TSVs, the leaf column is referenced by EXACTLY ONE of the
      161 (narrow, col 103) / 253 (wide, col 91) constraints — its own arity-2 chip lookup — and
      there only at tuple position 17, the `out0` DIGEST slot. It is an input to nothing; no gate, no
      boundary, no PI binding, no map-op mentions it. So the vestige is a DEAD PIN, not a wrong
      binding: it costs a Poseidon2 chip request per row and it makes a false claim, but it relaxes
      nothing.
  (3) Dropping it preserves everything this descriptor was relied on for
      (`heapSpliceImt_addr_forced`, `goodSpliceRow_recomputes_imt`).

⚠ **FLAG-DAY (NOT taken here, because it MOVES DEPLOYED DESCRIPTOR BYTES).** Emitting
`heapSpliceSitesImt` deletes one arity-2 `poseidon2_chip` lookup from `heapWriteVmDescriptor2R24` in
BOTH committed registries — narrow `circuit/descriptors/rotation-v3-staged-registry.tsv`
(`dregg-effectvm-heapWrite-splice-v1-rot24-v3-staged`, the lookup `arity 2, in0 102, in1 72, out0 103`)
and WIDE `rotation-wide-registry-staged.tsv`
(`dregg-effectvm-heapWrite-v1-rot24-v3-write-heapopen`, the same lookup compacted to
`in0 90, in1 72, out0 91`). The exact gated step, in order:
  1. flip `heapWriteSpliceVmDescriptor.hashSites` to `heapSpliceSitesImt`;
  2. regen — `lake env lean --run EmitRotationV3.lean` → `scripts/emit_descriptors.py`, which rewrites
     both TSVs + `circuit/descriptors/PROVENANCE.json`;
  3. drop the producer's `leaf_digest_col` fill (`trace_rotated.rs::generate_rotated_heap_write_wide_raw`
     lays `AUX_BASE + 13` = the compacted col 91) — Rust CALLS the emission, so this follows it;
  4. `heap_write_deployed_root_forced.rs` keeps its NEGATIVE assertion on `HEAP_LEAF` and gains a
     positive one that no arity-2 lookup targets it at all;
  5. ⚠ **VK EPOCH.** The descriptor bytes change ⇒ the verification key for `heapWriteVmDescriptor2R24`
     changes ⇒ every already-committed heapWrite turn was proven under the OLD VK. This is a
     VK-epoch flip, not a byte tidy-up, which is exactly why it is ember-gated and not done here.
The cheap, byte-safe alternative — leaving the lookup and calling it what it is — is what this section
does. -/

/-- The DEPLOYED heap leaf as a function: the ARITY-3 IMT leaf `hash[addr, value, next_addr]`. The
preimage ORDER is `heap_root.rs::HeapLeaf::preimage` = `[addr, value, next_addr]` (the single place the
schema is written, pinned Rust-side by `heap_leaf_schema_pin`), and the same order the emitted arity-3
chip lookup absorbs (`Emit.HeapOpenEmit.heapLeafInputs`, `#guard`-pinned at length 3). Stated locally
rather than imported so this file adds no import; it is `IndexedMerkleTree.imtLeafHash` on the nose. -/
def deployedImtLeafOf (hash : List ℤ → ℤ) (addr value next : ℤ) : ℤ := hash [ addr, value, next ]

/-- The emitted vestige's arity tag, pinned: 2. The deployed leaf's is 3 (`HEAP_LEAF_ARITY`). -/
theorem siteHeapLeaf_arity : siteHeapLeaf.arity = 2 := rfl

/-- **The preimages DIFFER, for every `(addr, value, next)` and every sponge.** The vestige absorbs a
2-element list; the deployed leaf absorbs a 3-element list. This is the arity wall at the leaf, stated
without any hash hypothesis — the same wall `MapAbsentImtGate.imtLeafHash_ne_heapLeafOf` lifts to
digests under CR and `MapReconcileImtRepoint.imtRoot_ne_mapRoot` lifts to roots. -/
theorem siteHeapLeaf_preimage_ne_deployed (addr value next : ℤ) :
    ([ addr, value ] : List ℤ) ≠ [ addr, value, next ] := by
  simp

/-- **★ THE SEPARATION, FLOOR-FREE, AT A NAMED SPONGE AND A NAMED WITNESS.** At the concrete sponge
`cN` and the §6 witness (`addr = cN [3,4]`, `value = 42`, terminal pointer `next = 2013265920` — the
deployed `SENTINEL_MAX`), the digest `siteHeapLeaf` forces is NOT the deployed arity-3 IMT leaf digest.
No `Poseidon2SpongeCR`, no existential: one specific pair, decided. So the vestige's digest is not the
committed leaf even on the honest row the producer lays. -/
theorem siteHeapLeaf_is_not_the_deployed_leaf :
    leafOf cN (addrOf cN 3 4) 42
      ≠ deployedImtLeafOf cN (addrOf cN 3 4) 42 2013265920 := by
  unfold leafOf deployedImtLeafOf addrOf cN
  norm_num

/-- The two emitted sites' input lists, `rfl`-pinned — the ground truth the next pin decides over. -/
theorem siteHeapAddr_inputs :
    siteHeapAddr.inputs = [ .col (prmCol hp.COLL), .col (prmCol hp.KEY) ] := rfl

/-- The vestige reads the ADDRESS carrier and the VALUE param — it does not read itself. -/
theorem siteHeapLeaf_inputs :
    siteHeapLeaf.inputs = [ .col HEAP_ADDR, .col (prmCol hp.VALUE) ] := rfl

/-- **★ THE VESTIGE IS UNREAD.** `HEAP_LEAF` occurs in `heapSpliceSites` ONLY as `siteHeapLeaf`'s
`digestCol` — no site absorbs it. Since `hashSites` is the descriptor's WHOLE hash layer
(`heapWriteSpliceVmDescriptor_hashSites`) and the splice `MapOp` appended downstream keys on
`HEAP_ADDR` and values on `prmCol hp.VALUE` (deployed-byte-checked in
`heap_write_deployed_root_forced.rs`), nothing in this circuit consumes the retired digest. That is why
the wrong-shaped site is a DEAD PIN and not a soundness hole — and also why deleting it is safe modulo
the VK epoch. -/
theorem heapSpliceSites_never_read_HEAP_LEAF :
    ∀ s ∈ heapSpliceSites, (HashInput.col HEAP_LEAF) ∉ s.inputs := by
  decide

/-! ### §8.1 — the POST-FLAG-DAY shape, authored now, emitted at the gated regen. -/

/-- **`heapSpliceSitesImt`** — the heapWrite recompute sites with the vestige DROPPED: the address site
alone. This is what `heapWriteSpliceVmDescriptor.hashSites` becomes at the ember-gated regen (the
flag-day above). Authored here so the Lean says the deployed shape BEFORE the bytes move, per house law
#1 (constraints are authored in Lean; Rust only calls the emission). -/
def heapSpliceSitesImt : List VmHashSite := [ siteHeapAddr ]

/-- **`heapWriteSpliceVmDescriptorImt`** — the post-flag-day base descriptor. NOT routed, NOT emitted:
`EmitRotationV3.lean` still emits `heapWriteV3` over `heapWriteSpliceVmDescriptor`, so no checked-in
byte moves by this definition existing. -/
def heapWriteSpliceVmDescriptorImt : EffectVmDescriptor :=
  { heapWriteSpliceVmDescriptor with hashSites := heapSpliceSitesImt }

/-- The flag-day is EXACTLY the removal of the trailing vestige — nothing is reordered, no other site
changes, so the address lookup's emitted coordinates are untouched. -/
theorem heapSpliceSites_is_imt_plus_vestige :
    heapSpliceSites = heapSpliceSitesImt ++ [ siteHeapLeaf ] := rfl

/-- The only difference between the two descriptors is the hash-site list. -/
theorem heapWriteSpliceVmDescriptorImt_differs_only_in_sites :
    heapWriteSpliceVmDescriptorImt.name = heapWriteSpliceVmDescriptor.name
    ∧ heapWriteSpliceVmDescriptorImt.traceWidth = heapWriteSpliceVmDescriptor.traceWidth
    ∧ heapWriteSpliceVmDescriptorImt.piCount = heapWriteSpliceVmDescriptor.piCount
    ∧ heapWriteSpliceVmDescriptorImt.constraints = heapWriteSpliceVmDescriptor.constraints
    ∧ heapWriteSpliceVmDescriptorImt.ranges = heapWriteSpliceVmDescriptor.ranges := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **★ THE LOAD-BEARING FORCING SURVIVES THE FLAG-DAY.** The address carrier — the splice `MapOp`'s
KEY, the one binding this descriptor is relied on for — is still forced by the REDUCED site list. So
dropping the vestige costs no soundness, which is the whole content of the regen being safe. -/
theorem heapSpliceImt_addr_forced (hash : List ℤ → ℤ) (env : VmRowEnv)
    (h : siteHoldsAll hash env heapSpliceSitesImt) :
    env.loc HEAP_ADDR = addrOf hash (env.loc (prmCol hp.COLL)) (env.loc (prmCol hp.KEY)) := by
  unfold heapSpliceSitesImt siteHoldsAll at h
  simp only [siteHoldsAll.go, siteHeapAddr,
    VmHashSite.resolvedInputs, HashInput.resolve, List.map_cons, List.map_nil] at h
  obtain ⟨h0, _⟩ := h
  rw [h0]; rfl

/-- **NON-VACUITY of the post-flag-day shape (witness TRUE).** The SAME concrete row satisfies the
reduced recompute — the flag-day does not strand the honest producer. -/
theorem goodSpliceRow_recomputes_imt : siteHoldsAll cN goodSpliceRow heapSpliceSitesImt := by
  have hC : prmCol hp.COLL = 70 := by decide
  have hK : prmCol hp.KEY = 71 := by decide
  have hA : HEAP_ADDR = 102 := by decide
  unfold heapSpliceSitesImt siteHoldsAll
  simp only [siteHoldsAll.go, siteHeapAddr,
    VmHashSite.resolvedInputs, HashInput.resolve, List.map_cons, List.map_nil,
    hC, hK, hA]
  refine ⟨?_, trivial⟩
  · show goodSpliceRow.loc 102 = cN [goodSpliceRow.loc 70, goodSpliceRow.loc 71]; decide

/-- A FORGED heap-write row: the same bound `(coll, key) = (3, 4)` as `goodSpliceRow`, but the
`HEAP_ADDR` carrier (col 102) left at 0 instead of the recompute — a prover trying to key the splice at
an address of its choosing. -/
def forgedAddrRow : VmRowEnv where
  loc := fun v => if v = 70 then 3 else if v = 71 then 4 else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- **NON-VACUITY (the REFUSING tooth at the reduced shape).** `forgedAddrRow` is REFUSED by
`heapSpliceSitesImt`: the reduced site list is not satisfied by everything, so dropping the vestige did
not drop the teeth. Derived THROUGH `heapSpliceImt_addr_forced`, so the tooth bites on exactly the
binding the flag-day must preserve. -/
theorem forgedAddrRow_refused_imt : ¬ siteHoldsAll cN forgedAddrRow heapSpliceSitesImt := by
  intro h
  have hforce := heapSpliceImt_addr_forced cN forgedAddrRow h
  have hA : HEAP_ADDR = 102 := by decide
  have hC : prmCol hp.COLL = 70 := by decide
  have hK : prmCol hp.KEY = 71 := by decide
  rw [hA, hC, hK] at hforce
  simp only [forgedAddrRow, addrOf] at hforce
  norm_num [cN] at hforce

/-! ## §9 — Axiom-hygiene + layout pins. -/

-- The new/old-root carriers ARE the absorbed `heap_root` (= cap-root) state columns.
#guard HEAP_ROOT_AFTER == EffectVmEmitCapRoot.CAP_ROOT_AFTER
#guard HEAP_ROOT_BEFORE == EffectVmEmitCapRoot.CAP_ROOT_BEFORE
-- The address / leaf / before / after carriers are DISTINCT.
#guard [HEAP_ADDR, HEAP_LEAF, HEAP_ROOT_BEFORE, HEAP_ROOT_AFTER].dedup.length == 4
-- The write param columns are distinct + in-range.
#guard [hp.COLL, hp.KEY, hp.VALUE].dedup.length == 3
#guard [hp.COLL, hp.KEY, hp.VALUE].all (· < NUM_PARAMS)
-- The EMITTED (checked-in-byte) recompute is two ordered sites (address, then the §8 vestige); the new
-- root is the splice `MapOp`. This `2` is a DEPLOYED-BYTE pin, not a target — the flag-day takes it to 1.
#guard heapSpliceSites.length == 2
-- The post-flag-day shape is the address site alone, and it is a PREFIX of the emitted list (§8's
-- `heapSpliceSites_is_imt_plus_vestige` is the `rfl` that says WHICH site is dropped).
#guard heapSpliceSitesImt.length == 1
-- The vestige's arity is 2; the deployed IMT leaf's is 3 (`heap_root.rs::HEAP_LEAF_ARITY`).
#guard siteHeapLeaf.arity == 2
#guard siteHeapAddr.arity == 2

#assert_axioms heapSplice_addr_forced
#assert_axioms heapSplice_leaf_forced
#assert_axioms goodSpliceRow_recomputes
#assert_axioms tampered_value_moves_leaf
#assert_axioms tampered_addr_moves_leaf
-- §8: the vestige, measured.
#assert_axioms siteHeapLeaf_preimage_ne_deployed
#assert_axioms siteHeapLeaf_is_not_the_deployed_leaf
#assert_axioms heapSpliceSites_never_read_HEAP_LEAF
#assert_axioms heapSpliceSites_is_imt_plus_vestige
#assert_axioms heapSpliceImt_addr_forced
#assert_axioms goodSpliceRow_recomputes_imt
#assert_axioms forgedAddrRow_refused_imt

end Dregg2.Circuit.Emit.EffectVmEmitHeapRoot

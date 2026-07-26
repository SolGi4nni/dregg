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

★ **THE ARITY-2 VESTIGE IS DELETED FROM THE DEPLOYED BYTES (2026-07-26, ember-authorized VK epoch).**
`siteHeapLeaf` was the leg NOT moved on 2026-07-12: a 1-felt ARITY-2 `hash[addr, value]` recompute
that was still EMITTED into all three committed registries and was no longer any leaf of any deployed
tree. `eee9bd863` measured it at byte level — referenced by EXACTLY ONE of the 161 (narrow) / 253
(wide) constraints, its own chip lookup, at the `out0` slot; no gate, boundary, PI binding or map-op
read it. A DEAD PIN: it relaxed nothing, it cost one Poseidon2 chip request per row, and it made a
false claim. Re-pointing it at arity 3 was refused as a felt-width REGRESSION (a second 1-felt
arity-3 site would be a strictly narrower commitment of a fact already forced at 8 felts), so the
correct flag-day was DELETION. `heapSpliceSites` is now the address site ALONE (§2.E) and §8 carries
the record: why the site was wrong, the pin that it is GONE, and the falsifier that re-adding it goes
RED. The VK for `heapWriteVmDescriptor2R24` moved with the bytes.

The new `heap_root` is FORCED — not by a prepend accumulator — but by a genuine `.write` `MapOp` whose
`Ir2Air::MapOps` AIR opens the addressed OLD leaf against the committed root and recomputes the sorted-tree
update (see `RotatedKernelRefinementExercise.heapWriteV3` + `DescriptorIR2.writesTo`).

ONE in-row recompute site (the cap-root gate family reused, `EffectVmEmitCapRoot`; the SAME
`VmHashSite` shape, the cap-edge leaf `hash[holder,target,rights,op]` replaced by the heap address
shape):

  1. **`siteHeapAddr`** — recompute the heap ADDRESS in-row: `addr = hash[ coll, key ]`. The prover
     cannot choose the address freely; it is `hash` of the bound `(collection_id, key)` (the design's
     "sorted-by-key-hash", `Substrate.Heap.addrOf`). This binds the splice `MapOp`'s KEY column, and
     it is the ONLY binding this descriptor's hash layer is relied on for.

## Where the new root is FORCED (the SPLICE, NOT a prepend digest)

The new `heap_root` is NOT advanced by a prepend accumulator `hash[leaf, old_root]` — that digest is a
function of `(leaf, old_root)` a prover can pick without performing the real sorted-tree insert. Instead
`heapWriteSpliceVmDescriptor` (§2.E) carries ONLY the address site and delegates the new-root
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
recomputes, so cell≡circuit is BY DEFINITION at that value layer (the cap Phase-A discipline). The
LEAF leg runs through the heap-open appendix (`HeapOpenEmit`) at the arity-3 IMT leaf — it never ran
through a §2 site again after the 07-26 deletion, which is the point of the deletion: there is now
exactly ONE place this descriptor commits a heap leaf, and it is the 8-felt one.
The Rust differential is `circuit/tests/heap_root_cell_circuit_differential.rs`
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

/-- The RETIRED heap-LEAF carrier — the aux slot past the address that the deleted arity-2 vestige
used to drive (§8). **No site and no constraint in this descriptor binds it any more**; it is named
here only so the structural tooth can pin its ABSENCE by column (`heapSpliceSites_have_no_HEAP_LEAF_site`,
and Rust-side `heap_write_deployed_root_forced.rs`). Do not allocate anything else to it without
retiring that tooth first. -/
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

/-! ## §2 — the ONE in-row recompute hash-site (the address; the new root is splice-forced). -/

/-- **`siteHeapAddr`** — `addr = hash[ coll, key ]` (the sorted address; `Substrate.Heap.addrOf`). -/
def siteHeapAddr : VmHashSite :=
  { digestCol := HEAP_ADDR
  , inputs := [ .col (prmCol hp.COLL), .col (prmCol hp.KEY) ]
  , arity := 2 }

/-- **`siteHeapLeaf`** — ⚠ **THE DELETED VESTIGE**, arity 2: `hash[ addr, value ]`
(`Substrate.Heap.leafOf`). NOT the deployed heap leaf, which is the arity-3 IMT leaf
`hash[addr, value, next_addr]` (`heap_root.rs::HeapLeaf::preimage`, `Emit.HeapOpenEmit.heapLeafInputs`).

**It is NOT in `heapSpliceSites` and therefore not in any descriptor byte.** It survives as a NAMED
OBJECT for exactly two jobs, both in §8: it is the subject of the separation theorems that say why the
site was wrong (`siteHeapLeaf_preimage_ne_deployed`, `siteHeapLeaf_is_not_the_deployed_leaf`), and it
is the FALSIFIER WITNESS for the structural tooth — `readding_siteHeapLeaf_breaks_the_tooth` is the
machine-checked "re-add the site → RED". Deleting this definition would make the tooth unfalsifiable,
which is why it is kept rather than swept. -/
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

The base descriptor carries the address site ALONE: `siteHeapAddr` binds the MapOp's KEY column
(`HEAP_ADDR = hash[coll, key]`) to the genuine sorted address — that is the load-bearing one, and
since the 07-26 flag-day it is the only one. The MapOps AIR recomputes the ARITY-3 leaf internally
along the opened path, and the heap-open appendix commits it at native 8-felt width; the new root is
FORCED by the splice alone — the content-binding a prepend digest could not give. -/

/-- The heapWrite recompute sites: the address site, and nothing else (the new-root advance is the
splice `MapOp`). `siteHeapAddr` binds the MapOp KEY (`HEAP_ADDR = hash[coll, key]`). **These are the
CHECKED-IN BYTES** — the arity-2 leaf vestige was DELETED here on 2026-07-26 (§8), which moved the
`heapWriteVmDescriptor2R24` bytes in all three committed registries and therefore its VK. -/
def heapSpliceSites : List VmHashSite := [ siteHeapAddr ]

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

/-- The RETIRED arity-2 leaf as a function of `(addr, value)` — what the DELETED site used to force.
⚠ Not the deployed leaf, and no longer forced by anything: it survives only as the left-hand side of
§8's separation theorems (`deployedImtLeafOf` is the deployed one). -/
def leafOf (hash : List ℤ → ℤ) (addr value : ℤ) : ℤ := hash [ addr, value ]

/-! ## §4 — the address carrier is FORCED by a satisfying splice row. -/

/-- **`heapSplice_addr_forced`** — the address carrier IS `hash[coll,key]` from the splice sites (the
MapOp KEY binding): a satisfying splice row binds `HEAP_ADDR` to the genuine sorted address, so the
`.write` MapOp's key is the real `hash[coll,key]`, not a free column. -/
theorem heapSplice_addr_forced (hash : List ℤ → ℤ) (env : VmRowEnv)
    (h : siteHoldsAll hash env heapSpliceSites) :
    env.loc HEAP_ADDR = addrOf hash (env.loc (prmCol hp.COLL)) (env.loc (prmCol hp.KEY)) := by
  unfold heapSpliceSites siteHoldsAll at h
  simp only [siteHoldsAll.go, siteHeapAddr,
    VmHashSite.resolvedInputs, HashInput.resolve, List.map_cons, List.map_nil] at h
  obtain ⟨h0, _⟩ := h
  rw [h0]; rfl

/- ⚠ **`heapSplice_leaf_forced` IS GONE (2026-07-26).** It said the `HEAP_LEAF` carrier is
`hash[addr, value]`, which was TRUE of the emitted bytes and about a digest no deployed tree uses. It
was the one theorem in this file whose NAME invited the wrong reading ("the heap leaf is forced"), and
with the site deleted it would be a theorem about a descriptor that no longer exists. The deployed leaf
binding is `HeapOpenEmit.heapLeafDigest_sound8` (arity 3, native 8 felts) — that is the only place to
cite. -/

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
`hash[coll,key]`. **The VALUE is bound by the splice `MapOp` itself** (`m.value = prmCol hp.VALUE`,
deployed-byte-checked in `heap_write_deployed_root_forced.rs`), NOT by any hash site — which is why
deleting the arity-2 leaf site cost nothing: the site never carried that binding either (§8). -/

/-! ## §6 — NON-VACUITY: a concrete splice row fires; a tampered key moves the address. -/

/-- A concrete heap-write splice row: coll=3 (col 70), key=4 (col 71), value=42 (col 72). The
address carrier (col 102) holds the genuine recomputed value under the toy sponge `cN`, so the splice
recompute holds. ⚠ Col 103 (the retired leaf carrier) is deliberately LEFT AT ZERO — the deployed
producer stopped filling it at the same flag-day
(`trace_rotated.rs::generate_rotated_heap_write_wide_raw`), so the witness row mirrors the producer. -/
def goodSpliceRow : VmRowEnv where
  loc := fun v =>
    if v = 70 then 3
    else if v = 71 then 4
    else if v = 72 then 42
    else if v = 102 then cN [3, 4]
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

-- The witness row's literal columns ARE the symbolic carrier columns (anti-drift).
#guard prmCol hp.COLL == 70
#guard prmCol hp.KEY == 71
#guard prmCol hp.VALUE == 72
#guard HEAP_ADDR == 102

/-- **NON-VACUITY (witness TRUE).** `goodSpliceRow` satisfies the address recompute under the concrete
sponge — the site carries its genuine digest. The recompute predicate is INHABITED. -/
theorem goodSpliceRow_recomputes : siteHoldsAll cN goodSpliceRow heapSpliceSites := by
  have hC : prmCol hp.COLL = 70 := by decide
  have hK : prmCol hp.KEY = 71 := by decide
  have hA : HEAP_ADDR = 102 := by decide
  unfold heapSpliceSites siteHoldsAll
  simp only [siteHoldsAll.go, siteHeapAddr,
    VmHashSite.resolvedInputs, HashInput.resolve, List.map_cons, List.map_nil,
    hC, hK, hA]
  refine ⟨?_, trivial⟩
  · show goodSpliceRow.loc 102 = cN [goodSpliceRow.loc 70, goodSpliceRow.loc 71]; decide

/-- **NON-VACUITY (anti-ghost on the address, the SURVIVING binding).** A different bound `(coll, key)`
(3,4 → 5,6) recomputes to a different `HEAP_ADDR`, so it keys the splice `MapOp` at a different leaf —
the prover cannot re-aim a write by moving the params. This replaces the two retired
`tampered_*_moves_leaf` theorems, which were anti-ghosts at the DELETED arity-2 leaf: they were about a
digest no deployed tree folds, and the value's anti-ghost is the splice's (`writesTo_functional` /
`MapPaddedDenotation.writesToMerkleS_functional_of_good`), never a hash site's. -/
theorem tampered_key_moves_addr : addrOf cN 3 4 ≠ addrOf cN 5 6 := by
  unfold addrOf cN
  norm_num

/-! ## §8 — ⚑ THE VESTIGE, DELETED: the flag-day record and the tooth that keeps it deleted.

This section exists because the site was on the EMIT side. `heapWriteSpliceVmDescriptor` is the byte
source of a descriptor the deployed light client resolves, so "the Lean names the wrong object" here was
one step from "the descriptor models the wrong object". `eee9bd863` established, machine-checked, that
it was the first and not the second, and this section keeps that record — because it is the
JUSTIFICATION for the deletion, not decoration on it:

  (1) `siteHeapLeaf` absorbed a preimage the deployed leaf does NOT have (`siteHeapLeaf_arity`,
      `siteHeapLeaf_preimage_ne_deployed`) and its digest genuinely differs at a NAMED sponge and a
      NAMED witness (`siteHeapLeaf_is_not_the_deployed_leaf`) — no floor, no existential.
  (2) NOTHING read the column it drove. Measured across the WHOLE committed constraint list, not just
      the hash layer: decoding the registry TSVs at `eee9bd863`, the leaf column was referenced by
      EXACTLY ONE of the 161 (narrow, col 103) / 253 (wide, col 91) constraints — its own arity-2 chip
      lookup — and there only at tuple position 17, the `out0` DIGEST slot. It was an input to nothing;
      no gate, no boundary, no PI binding, no map-op mentioned it. A DEAD PIN, not a wrong binding: it
      cost a Poseidon2 chip request per row and it made a false claim, but it relaxed nothing. That is
      why the deletion is a byte move with no soundness content — and why re-POINTING it at arity 3
      was refused instead: a second 1-felt arity-3 site would be a strictly NARROWER commitment of a
      fact the heap-open appendix already forces at 8 felts, i.e. a felt-width regression.
  (3) Everything this descriptor is relied on for survives: `heapSplice_addr_forced` (the splice
      `MapOp`'s KEY binding), `goodSpliceRow_recomputes` (the honest producer is not stranded),
      `forgedAddrRow_refused` (the tooth still bites, derived THROUGH the surviving forcing).

★ **THE FLAG-DAY, TAKEN 2026-07-26 (ember-authorized VK epoch).** `heapSpliceSites` is now
`[ siteHeapAddr ]`, which deleted one arity-2 `poseidon2_chip` lookup from `heapWriteVmDescriptor2R24`
in all THREE committed registries — narrow `circuit/descriptors/rotation-v3-staged-registry.tsv`
(`dregg-effectvm-heapWrite-splice-v1-rot24-v3-staged`, the lookup `arity 2, in0 102, in1 72, out0 103`),
WIDE `rotation-wide-registry-staged.tsv` and the UMEM-WELDED
`rotation-wide-umem-welded-registry-staged.tsv` (the same lookup compacted to `in0 90, in1 72,
out0 91`; the welded member was NOT in the flag-day recipe and is corrected here). Steps taken, in
order: this flip; `scripts/emit_descriptors.py` under `DREGG_VK_REGEN_ACK`, which rewrote the three
TSVs + the `*_FP` pins + `PROVENANCE.json` and appended the `docs/VK-REGEN-LOG.md` row; the producer's
now-dead `leaf_digest_col` fill dropped in `trace_rotated.rs`; the structural tooth extended and made
falsifiable.

⚠ **THE VK CONSEQUENCE, STATED PLAINLY.** The descriptor bytes moved ⇒ the AIR fingerprint feeding
`compute_recursive_vk_hash` moved ⇒ the verification key for `heapWriteVmDescriptor2R24` moved ⇒ any
already-committed heapWrite turn was proven under the OLD VK and does not verify under the new one.
Priced against reality (the `498d27a2b8` / `f97c561c8b` precedent): nothing is deployed and the devnet
ledger was already lost on reboot, so this costs a RE-GENESIS, not a migration. For THIS descriptor the
reading is stronger still — there is no `Effect::HeapWrite` variant at all, so no live selector reaches
it and NO committed turn of this member exists to migrate (it is reached only through the
exercise-inner heap-write path and the dedicated wide producer). -/

/-- The DEPLOYED heap leaf as a function: the ARITY-3 IMT leaf `hash[addr, value, next_addr]`. The
preimage ORDER is `heap_root.rs::HeapLeaf::preimage` = `[addr, value, next_addr]` (the single place the
schema is written, pinned Rust-side by `heap_leaf_schema_pin`), and the same order the emitted arity-3
chip lookup absorbs (`Emit.HeapOpenEmit.heapLeafInputs`, `#guard`-pinned at length 3). Stated locally
rather than imported so this file adds no import; it is `IndexedMerkleTree.imtLeafHash` on the nose. -/
def deployedImtLeafOf (hash : List ℤ → ℤ) (addr value next : ℤ) : ℤ := hash [ addr, value, next ]

/-- The deleted vestige's arity tag, pinned: 2. The deployed leaf's is 3 (`HEAP_LEAF_ARITY`). -/
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
No `Poseidon2SpongeCR`, no existential: one specific pair, decided. So the vestige's digest was not the
committed leaf even on the honest row the producer laid — which is the whole content of "it made a false
claim", and the reason the site is gone rather than renamed. -/
theorem siteHeapLeaf_is_not_the_deployed_leaf :
    leafOf cN (addrOf cN 3 4) 42
      ≠ deployedImtLeafOf cN (addrOf cN 3 4) 42 2013265920 := by
  unfold leafOf deployedImtLeafOf addrOf cN
  norm_num

/-- The emitted site's input list, `rfl`-pinned — the ground truth the tooth decides over. -/
theorem siteHeapAddr_inputs :
    siteHeapAddr.inputs = [ .col (prmCol hp.COLL), .col (prmCol hp.KEY) ] := rfl

/-- The deleted vestige's input list, kept as the falsifier witness's shape (it read the ADDRESS carrier
and the VALUE param). -/
theorem siteHeapLeaf_inputs :
    siteHeapLeaf.inputs = [ .col HEAP_ADDR, .col (prmCol hp.VALUE) ] := rfl

/-! ### §8.1 — ⚑ THE STRUCTURAL TOOTH: the vestige is GONE, and the tooth can go RED.

`hashSites` is the descriptor's WHOLE hash layer (`heapWriteSpliceVmDescriptor_hashSites`), so a pin over
`heapSpliceSites` is a pin over every hash site the emitted bytes carry. Two directions, both decided:

  * **the tooth** — no site drives `HEAP_LEAF` and no site absorbs it, so the retired leaf column is
    bound by nothing in this circuit's hash layer;
  * **the falsifier** — the SAME predicate over `heapSpliceSites ++ [ siteHeapLeaf ]` (literally
    "re-add the deleted site") is FALSE. A pin that cannot go red is not a gate, so the refutation is
    stated as a theorem rather than left to a hand experiment.

The Rust half, over the DEPLOYED BYTES rather than the site list, is
`circuit/tests/heap_write_deployed_root_forced.rs` (`deployed_heapwrite_has_no_arity2_leaf_lookup` +
its in-test falsifier, which splices the retired lookup back into the parsed descriptor and asserts the
predicate flips). -/

/-- **★ THE VESTIGE IS ABSENT FROM THE EMITTED HASH LAYER.** No site in `heapSpliceSites` drives
`HEAP_LEAF` as its digest, and none absorbs it as an input. Combined with
`heapWriteSpliceVmDescriptor_hashSites` (these sites ARE the whole hash layer) and the splice `MapOp`
keying on `HEAP_ADDR` / valuing on `prmCol hp.VALUE` (deployed-byte-checked in
`heap_write_deployed_root_forced.rs`), the retired arity-2 leaf digest is emitted NOWHERE and read
NOWHERE. -/
theorem heapSpliceSites_have_no_HEAP_LEAF_site :
    ∀ s ∈ heapSpliceSites,
      s.digestCol ≠ HEAP_LEAF ∧ (HashInput.col HEAP_LEAF) ∉ s.inputs := by
  decide

/-- **★ THE FALSIFIER — re-adding the site goes RED.** The predicate
`heapSpliceSites_have_no_HEAP_LEAF_site` decides over is FALSE of the pre-flag-day list
(`heapSpliceSites ++ [ siteHeapLeaf ]`, exactly the emitted list before 2026-07-26). So the tooth is
REFUTABLE, not vacuously true of every site list: a regression that re-emits the vestige — by editing
`heapSpliceSites` or by any refactor that re-introduces an arity-2 site at `HEAP_LEAF` — makes the tooth
above fail to elaborate. -/
theorem readding_siteHeapLeaf_breaks_the_tooth :
    ¬ (∀ s ∈ heapSpliceSites ++ [ siteHeapLeaf ],
        s.digestCol ≠ HEAP_LEAF ∧ (HashInput.col HEAP_LEAF) ∉ s.inputs) := by
  decide

/-- A FORGED heap-write row: the same bound `(coll, key) = (3, 4)` as `goodSpliceRow`, but the
`HEAP_ADDR` carrier (col 102) left at 0 instead of the recompute — a prover trying to key the splice at
an address of its choosing. -/
def forgedAddrRow : VmRowEnv where
  loc := fun v => if v = 70 then 3 else if v = 71 then 4 else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- **NON-VACUITY (the REFUSING tooth at the post-flag-day shape).** `forgedAddrRow` is REFUSED by
`heapSpliceSites`: the reduced site list is not satisfied by everything, so deleting the vestige did not
delete the teeth. Derived THROUGH `heapSplice_addr_forced`, so the tooth bites on exactly the binding the
flag-day had to preserve. -/
theorem forgedAddrRow_refused : ¬ siteHoldsAll cN forgedAddrRow heapSpliceSites := by
  intro h
  have hforce := heapSplice_addr_forced cN forgedAddrRow h
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
-- The address / retired-leaf / before / after carriers are DISTINCT (the retired slot is still named,
-- so nothing may be re-allocated onto it while §8.1's tooth pins its emptiness).
#guard [HEAP_ADDR, HEAP_LEAF, HEAP_ROOT_BEFORE, HEAP_ROOT_AFTER].dedup.length == 4
#guard HEAP_LEAF == 103
-- The write param columns are distinct + in-range.
#guard [hp.COLL, hp.KEY, hp.VALUE].dedup.length == 3
#guard [hp.COLL, hp.KEY, hp.VALUE].all (· < NUM_PARAMS)
-- The EMITTED (checked-in-byte) recompute is ONE site — the address; the new root is the splice `MapOp`.
-- This `1` is a DEPLOYED-BYTE pin: it was `2` until the 2026-07-26 vestige deletion (§8).
#guard heapSpliceSites.length == 1
-- The deleted vestige's arity was 2; the deployed IMT leaf's is 3 (`heap_root.rs::HEAP_LEAF_ARITY`).
#guard siteHeapLeaf.arity == 2
#guard siteHeapAddr.arity == 2

#assert_axioms heapSplice_addr_forced
#assert_axioms goodSpliceRow_recomputes
#assert_axioms tampered_key_moves_addr
-- §8: why the vestige was wrong, and the tooth that keeps it deleted.
#assert_axioms siteHeapLeaf_preimage_ne_deployed
#assert_axioms siteHeapLeaf_is_not_the_deployed_leaf
#assert_axioms heapSpliceSites_have_no_HEAP_LEAF_site
#assert_axioms readding_siteHeapLeaf_breaks_the_tooth
#assert_axioms forgedAddrRow_refused

end Dregg2.Circuit.Emit.EffectVmEmitHeapRoot

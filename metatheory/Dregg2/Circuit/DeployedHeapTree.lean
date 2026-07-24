import Dregg2.Circuit.DeployedCapTree
import Dregg2.Circuit.CapMerkleGeneric

/-!
# `DeployedHeapTree` — the native 8-felt heap-tree spine (Phase H-HEAP-8).

The SECOND faithful root's Lean spine, the exact twin of `DeployedCapTree`'s `Cap8Scheme`. The
deployed heap tree is a sorted-Poseidon2 binary Merkle map over LINKED IMT leaves
`(addr, value, nextAddr)` (`heap_root.rs::HeapLeaf` — the gap-#5 indexed-Merkle-tree rewiring:
the third field is the POINTER to the next-larger present address, the sorted-linked-list link
`IndexedMerkleTree.ImtLeaf`/`imtLeafHash`; nodes `mapNode hash l r = hash [l, r]`). The
historical commitment projected each node/leaf to a SINGLE felt (`hash : List ℤ → ℤ`, ~2^31), well
below the deployed FRI/STARK ~124-bit soundness floor: two genuinely-different heaps can collide on
the 1-felt root while topping different 8-felt roots (the heap GENTIAN tooth
`circuit/tests/heap_root_gentian_weld.rs` exhibits a concrete pair). This module gives the FAITHFUL
8-felt heap tree — every node absorbs full 8-felt children through the arity-16 `node8` chip and emits
a full 8-felt digest.

⚑ **THE `chip8CR` FIELD IS GONE (2026-07-20), AND THE STRUCTURE IS NOW INHABITED.** `Heap8Scheme` used
to carry `chip8CR : Compress8CR chipAbsorb8` as a FIELD — injectivity of a map that squeezes the
infinite `List ℤ` into 8 bounded BabyBear lanes. `VacuitySweepTeeth.compress8CR_false_babyBear` refutes
that for ANY function of that shape, the deployed chip included, so NO deployed `Heap8Scheme` value
could be constructed and every theorem of the form `∀ S8 : Heap8Scheme, …` — the whole heap-open
surface the sorted-tree forcing leans on — was VACUOUS. §H.D below exhibits `deployedHeap8Scheme`, a
real value whose OWN chip the teeth refute. The binding the tree used to ASSUME is now EXTRACTED AS
DATA: see `DeployedCapTree.Coll8` and the `…_binds_or_collides` family.

REUSE (the Option-A payoff, exactly as for cap): the membership-recompose anti-ghost spine is
digest-type-AGNOSTIC and already proved once — `CapMerkleGeneric.recomposeGFind`/`recomposeGFind_spec`,
the TOTAL-FUNCTION peel — so the heap tree instantiates it rather than re-authoring a parallel copy.
`Digest8`, `Compress8CR`, `Coll8`, and `pack8`/`pack8_inj` are shared verbatim from `DeployedCapTree` —
cap/heap/fields all ride the ONE `node8` compression (`descriptor_ir2::chip_absorb_all_lanes` at
`CHIP_NODE8_ARITY = 16`), which is also why §H.D's inhabitant rides the SAME deployed-shaped chip the
cap inhabitant does.
-/

namespace Dregg2.Circuit.DeployedHeapTree

open Dregg2.Circuit.DeployedCapTree (Digest8 Compress8CR Coll8 BABYBEAR_P deployedShapedChip8)
open Dregg2.Circuit.DeployedCapTree.Cap8Scheme (pack8 pack8_inj coll8_refutable_of_injective)

/-- **`Heap8Scheme`** — the native-8-felt heap-tree's SINGLE Poseidon2 carrier: the 8-output chip
absorb `chipAbsorb8 : List ℤ → Digest8` (`descriptor_ir2::chip_absorb_all_lanes`, all 8 squeezed
lanes). BOTH the leaf (`heapLeafDigest8`, arity 3 — the IMT `[addr, value, nextAddr]`) and the node
(`heapNodeOf8`, arity 16) ride it; the input lists are length-disjoint (3 vs 16), so the chip's
per-row `(arity, padded inputs)` seeding separates the two domains for free. The exact twin of
`DeployedCapTree.Cap8Scheme` — indeed the SAME carrier (one `node8` chip serves cap/heap/fields).

⚑ **ONE FIELD, AND IT IS INHABITED.** The `chip8CR : Compress8CR chipAbsorb8` field is DELETED — see
this module's header for why it made the type uninhabitable, and §H.D for the real value that now
inhabits it and whose own chip refutes the deleted claim
(`VacuitySweepTeeth.deployedHeap8Scheme_chip_not_Compress8CR`). -/
structure Heap8Scheme where
  /-- The single 8-output chip-absorb compression (`heap_root.rs::heap_node8`/`HeapLeaf::digest8`). -/
  chipAbsorb8 : List ℤ → Digest8

namespace Heap8Scheme

variable (S8 : Heap8Scheme)

/-- **`heapLeafDigest8 S8 e`** — the 8-felt deployed heap leaf digest, the SINGLE 8-output chip absorb
over the 3 LINKED-leaf fields `[addr, value, nextAddr]` (the gap-#5 IMT leaf — the pointer is IN the
digest, `IndexedMerkleTree.imtLeafHash`'s 8-felt twin). BYTE-IDENTICAL to
`heap_root.rs::HeapLeaf::digest8` (`chip_absorb_all_lanes(3, [addr, value, next_addr])`). -/
def heapLeafDigest8 (e : ℤ × ℤ × ℤ) : Digest8 := S8.chipAbsorb8 [e.1, e.2.1, e.2.2]

/-- **`heapNodeOf8 S8 l r`** — the native 8-felt internal node, the arity-16 chip absorb over
`pack8 l r = L8 ‖ R8`. BYTE-IDENTICAL to `heap_root.rs::heap_node8`. The SAME `chipAbsorb8` carrier as
the leaf — one heap hash everywhere. The 8-felt faithful twin of `MapMerkleRoot.mapNode`. -/
def heapNodeOf8 (l r : Digest8) : Digest8 := S8.chipAbsorb8 (pack8 l r)

/-- The IMT leaf block `[addr, value, nextAddr]` is injective in the triple — pure list/product
plumbing, no crypto. Factored out because BOTH the binding extractor and its strength bridge need it. -/
theorem heapLeafBlock_inj {e₁ e₂ : ℤ × ℤ × ℤ}
    (h : [e₁.1, e₁.2.1, e₁.2.2] = [e₂.1, e₂.2.1, e₂.2.2]) : e₁ = e₂ := by
  simp only [List.cons.injEq, and_true] at h
  exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2)

/-! ### §H.X — BINDING, EXTRACTED AS DATA (the sound replacement for the deleted injectivity family).

The four theorems this section replaces — `heapLeafDigest8_injective`, `heapNodeOf8_injective`,
`recomposeUp8_inj_of_path`, `membersAt8_functional_on_path` — were ALL discharged from the `chip8CR`
FIELD, i.e. from `Compress8CR chipAbsorb8`, which the deployed chip refutes. They are DELETED, not kept
beside the new forms: keeping them is what would make this regrounding additive and therefore inert.

Each is replaced by a TOTAL EXTRACTOR plus a theorem that what it returns is a genuine collision. The
conclusions are disjunctions `binding ∨ Coll8 chipAbsorb8 (the pair the extractor returned)`. As
FORMULAS they are weaker than the equalities they replace; as CONTENT AT DEPLOYED PARAMETERS they are
strictly stronger, because the deleted premise is unsatisfiable by the real chip — the old theorems
said nothing about the deployed system, and these hold OF it. §H.S proves that relation both ways. -/

/-- The heap-leaf extractor: the two arity-3 IMT blocks the chip absorbed. -/
def heapLeafColl8Find (e₁ e₂ : ℤ × ℤ × ℤ) : List ℤ × List ℤ :=
  ([e₁.1, e₁.2.1, e₁.2.2], [e₂.1, e₂.2.1, e₂.2.2])

/-- **Heap-leaf binding at 8-felt width, UNCONDITIONAL** (replaces `heapLeafDigest8_injective`). Equal
8-felt leaf digests EITHER force the whole LINKED triple equal — `addr`, `value`, AND the sorted-chain
POINTER, so a prover cannot relink the chain while keeping the leaf — OR the two arity-3 IMT blocks ARE
a genuine collision of the deployed chip, handed back by name. -/
theorem heapLeafDigest8_binds_or_collides {e₁ e₂ : ℤ × ℤ × ℤ}
    (h : heapLeafDigest8 S8 e₁ = heapLeafDigest8 S8 e₂) :
    e₁ = e₂ ∨ Coll8 S8.chipAbsorb8 (heapLeafColl8Find e₁ e₂) := by
  by_cases he : e₁ = e₂
  · exact Or.inl he
  · exact Or.inr ⟨fun hf => he (heapLeafBlock_inj hf), h⟩

/-- The heap-node extractor: the two arity-16 `L8 ‖ R8` input blocks. -/
def heapNodeColl8Find (l₁ r₁ l₂ r₂ : Digest8) : List ℤ × List ℤ := (pack8 l₁ r₁, pack8 l₂ r₂)

/-- **Heap-node binding at 8-felt width, UNCONDITIONAL** (replaces `heapNodeOf8_injective`, the "SOLE
width-specific obligation" the whole native-8-felt heap tree used to ride). Equal `node8` images EITHER
force equal 8-felt children, OR the two packed arity-16 blocks ARE a genuine chip collision. -/
theorem heapNodeOf8_binds_or_collides {l₁ r₁ l₂ r₂ : Digest8}
    (h : heapNodeOf8 S8 l₁ r₁ = heapNodeOf8 S8 l₂ r₂) :
    (l₁ = l₂ ∧ r₁ = r₂) ∨ Coll8 S8.chipAbsorb8 (heapNodeColl8Find l₁ r₁ l₂ r₂) := by
  by_cases hn : l₁ = l₂ ∧ r₁ = r₂
  · exact Or.inl hn
  · exact Or.inr ⟨fun hp => hn (pack8_inj hp), h⟩

/-- **`recomposeUp8 S8 cur path`** — the native-8-felt heap membership recompose, DEFINED as the
generic `CapMerkleGeneric.recomposeG` at `D := Digest8`, `node := heapNodeOf8 S8`. No bespoke
recursion — the SAME generic spine cap rides. BYTE-IDENTICAL to `heap_root.rs::recompose_membership_8`
and to the deployed in-circuit `node8` MapOps chain (unified onto `BUS_P2`). -/
def recomposeUp8 (cur : Digest8) (path : List (CapMerkleGeneric.StepG Digest8)) : Digest8 :=
  CapMerkleGeneric.recomposeG (heapNodeOf8 S8) cur path

/-- **The native-8-felt heap spine EXTRACTOR** — the generic path walk
(`CapMerkleGeneric.recomposeGFind`) at `node := heapNodeOf8 S8`, with the colliding child-pairs it lands
on mapped through `pack8` into the two arity-16 chip input blocks. A TOTAL function of the two starting
digests and the path. REUSED, not re-authored: the walk is proved once, generically. -/
def recomposeUp8Find (a b : Digest8) (path : List (CapMerkleGeneric.StepG Digest8)) :
    List ℤ × List ℤ :=
  (pack8 (CapMerkleGeneric.recomposeGFind (heapNodeOf8 S8) a b path).1.1
         (CapMerkleGeneric.recomposeGFind (heapNodeOf8 S8) a b path).1.2,
   pack8 (CapMerkleGeneric.recomposeGFind (heapNodeOf8 S8) a b path).2.1
         (CapMerkleGeneric.recomposeGFind (heapNodeOf8 S8) a b path).2.2)

/-- **The native-8-felt heap anti-ghost spine, UNCONDITIONAL** (replaces `recomposeUp8_inj_of_path`).
Equal recomposed roots along a FIXED path EITHER force equal starting 8-felt digests, OR the walk LANDS
on a level whose two arity-16 `node8` blocks are a genuine chip collision, returned by name. A prover
cannot keep the published 8-felt heap root while swapping the opened leaf UNLESS the deployed chip
actually collides at the two blocks this extractor hands back.

Still a PURE RE-INSTANTIATION — `CapMerkleGeneric.recomposeGFind_spec` is proved once, generically. -/
theorem recomposeUp8_binds_or_collides (path : List (CapMerkleGeneric.StepG Digest8))
    {a b : Digest8} (h : recomposeUp8 S8 a path = recomposeUp8 S8 b path) :
    a = b ∨ Coll8 S8.chipAbsorb8 (recomposeUp8Find S8 a b path) := by
  rcases CapMerkleGeneric.recomposeGFind_spec (heapNodeOf8 S8) path h with heq | ⟨hne, himg⟩
  · exact Or.inl heq
  · refine Or.inr ⟨fun hp => hne ?_, himg⟩
    exact Prod.ext (pack8_inj hp).1 (pack8_inj hp).2

/-- **THE HEAP-OPEN EXTRACTOR** — the SINGLE named pair the whole heap-open peel hands back. Run the
spine walk over the two leaf digests; if it found a genuine collision that is the answer, otherwise the
walk has already forced the two leaf DIGESTS equal, so the collision (if any) is at the leaf absorb and
the two arity-3 IMT blocks are the pair. -/
def heapOpen8Find (e₁ e₂ : ℤ × ℤ × ℤ) (path : List (CapMerkleGeneric.StepG Digest8)) :
    List ℤ × List ℤ :=
  if Coll8 S8.chipAbsorb8
      (recomposeUp8Find S8 (heapLeafDigest8 S8 e₁) (heapLeafDigest8 S8 e₂) path)
  then recomposeUp8Find S8 (heapLeafDigest8 S8 e₁) (heapLeafDigest8 S8 e₂) path
  else heapLeafColl8Find e₁ e₂

/-- **`HeapOpenColl S8 e₁ e₂ path`** — the pair `heapOpen8Find` RETURNS on this equivocation is a
genuine collision of the deployed arity-16 chip. The ONE named disjunct every heap-open consumer carries
in place of the deleted `chip8CR` floor. -/
def HeapOpenColl (e₁ e₂ : ℤ × ℤ × ℤ) (path : List (CapMerkleGeneric.StepG Digest8)) : Prop :=
  Coll8 S8.chipAbsorb8 (heapOpen8Find S8 e₁ e₂ path)

/-- **⚑ THE GENTIAN CLOSE, UNCONDITIONAL** (replaces `membersAt8_functional_on_path`). Two LINKED heap
leaves opening the SAME 8-felt root along the SAME committed path are EITHER the same leaf (addr, value,
AND pointer), OR the deployed chip genuinely collides at the two blocks `heapOpen8Find` hands back.

This is what the 8-felt migration actually buys, stated honestly: the lane-0 forge the GENTIAN tooth
exhibits (`circuit/tests/heap_root_gentian_weld.rs` — different entries, same 1-felt projection) is
excluded UNLESS the adversary produces a full ~124-bit collision at a NAMED pair of arity-16 blocks. The
old form asserted the exclusion outright while resting on a premise the deployed chip refutes. -/
theorem heapOpen8_binds_leaf_or_collides (path : List (CapMerkleGeneric.StepG Digest8))
    {e₁ e₂ : ℤ × ℤ × ℤ}
    (h : recomposeUp8 S8 (heapLeafDigest8 S8 e₁) path
       = recomposeUp8 S8 (heapLeafDigest8 S8 e₂) path) :
    e₁ = e₂ ∨ HeapOpenColl S8 e₁ e₂ path := by
  by_cases hif : Coll8 S8.chipAbsorb8
      (recomposeUp8Find S8 (heapLeafDigest8 S8 e₁) (heapLeafDigest8 S8 e₂) path)
  · refine Or.inr ?_
    show Coll8 S8.chipAbsorb8 (heapOpen8Find S8 e₁ e₂ path)
    rw [heapOpen8Find, if_pos hif]
    exact hif
  · rcases recomposeUp8_binds_or_collides S8 path h with hdig | hc
    · rcases heapLeafDigest8_binds_or_collides S8 hdig with he | hec
      · exact Or.inl he
      · refine Or.inr ?_
        show Coll8 S8.chipAbsorb8 (heapOpen8Find S8 e₁ e₂ path)
        rw [heapOpen8Find, if_neg hif]
        exact hec
    · exact absurd hc hif

/-- **`MembersAt8 S8 root e`** — the native-8-felt deployed heap-tree membership of a `(addr, value)`
PAIR: SOME linked leaf `(addr, value, next)` opens against the FULL 8-felt `root` (the IMT pointer is
existential at the map level — a map speaks `key → value`; the pointer is the sorted-chain plumbing).
The HONEST 8-felt replacement for the lossy 1-felt opening — opens against ~124-bit of root, not
lane-0. The heap twin of `DeployedCapTree.Cap8Scheme.MembersAt8`. -/
def MembersAt8 (root : Digest8) (e : ℤ × ℤ) : Prop :=
  ∃ (next : ℤ) (path : List (CapMerkleGeneric.StepG Digest8)),
    recomposeUp8 S8 (heapLeafDigest8 S8 (e.1, e.2, next)) path = root

/-! ### §H.S — THE STRENGTH RELATION, both directions (no strength lost; no free pass gained).

Deleting a carrier and restating its consumers as disjunctions invites two fair objections, both
answered here in Lean rather than in prose.

1. *"You weakened the theorems to make the deletion easy."* — the `…_of_injective` bridges assume
   exactly the injectivity the deleted field asserted, and each deleted theorem falls straight out.
   They are precisely the injective special case of the new ones.
2. *"The right disjunct is a free pass, so the disjunction says nothing."* —
   `heapOpenColl_refutable_of_injective` shows the collision disjunct is REFUTABLE: at an injective chip
   the extracted pair is NOT a collision, so the binding half has to do the work.

These are STANDALONE bridges, deliberately NOT hypotheses on any deployed keystone: `Compress8CR` is
FALSE at deployed BabyBear parameters, so a keystone carrying it would be right back where this repair
started. (The refutability core `coll8_refutable_of_injective` is shared verbatim from the cap tree —
`Coll8` is one predicate, not three.) -/

/-- **(CANARY at the heap-open composite.)** `HeapOpenColl` is refutable at an injective chip. -/
theorem heapOpenColl_refutable_of_injective (hCR : Compress8CR S8.chipAbsorb8)
    (e₁ e₂ : ℤ × ℤ × ℤ) (path : List (CapMerkleGeneric.StepG Digest8)) :
    ¬ HeapOpenColl S8 e₁ e₂ path :=
  coll8_refutable_of_injective hCR _

/-- **NO STRENGTH LOST — the deleted `heapLeafDigest8_injective` is the injective special case.** -/
theorem heapLeafDigest8_injective_of_injective (hCR : Compress8CR S8.chipAbsorb8)
    {e₁ e₂ : ℤ × ℤ × ℤ} (h : heapLeafDigest8 S8 e₁ = heapLeafDigest8 S8 e₂) : e₁ = e₂ := by
  rcases heapLeafDigest8_binds_or_collides S8 h with he | hc
  · exact he
  · exact absurd hc (coll8_refutable_of_injective hCR _)

/-- **NO STRENGTH LOST — the deleted `heapNodeOf8_injective` is the injective special case.** -/
theorem heapNodeOf8_injective_of_injective (hCR : Compress8CR S8.chipAbsorb8)
    {l₁ r₁ l₂ r₂ : Digest8} (h : heapNodeOf8 S8 l₁ r₁ = heapNodeOf8 S8 l₂ r₂) :
    l₁ = l₂ ∧ r₁ = r₂ := by
  rcases heapNodeOf8_binds_or_collides S8 h with hn | hc
  · exact hn
  · exact absurd hc (coll8_refutable_of_injective hCR _)

/-- **NO STRENGTH LOST — the deleted `recomposeUp8_inj_of_path` is the injective special case.** -/
theorem recomposeUp8_inj_of_path_of_injective (hCR : Compress8CR S8.chipAbsorb8)
    (path : List (CapMerkleGeneric.StepG Digest8)) {a b : Digest8}
    (h : recomposeUp8 S8 a path = recomposeUp8 S8 b path) : a = b := by
  rcases recomposeUp8_binds_or_collides S8 path h with heq | hc
  · exact heq
  · exact absurd hc (coll8_refutable_of_injective hCR _)

/-- **NO STRENGTH LOST at the composite** — the deleted `membersAt8_functional_on_path` (the GENTIAN
close) is the injective special case of `heapOpen8_binds_leaf_or_collides`. -/
theorem membersAt8_functional_on_path_of_injective (hCR : Compress8CR S8.chipAbsorb8)
    (root : Digest8) {e₁ e₂ : ℤ × ℤ × ℤ}
    (path : List (CapMerkleGeneric.StepG Digest8))
    (h₁ : recomposeUp8 S8 (heapLeafDigest8 S8 e₁) path = root)
    (h₂ : recomposeUp8 S8 (heapLeafDigest8 S8 e₂) path = root) : e₁ = e₂ := by
  rcases heapOpen8_binds_leaf_or_collides S8 path (h₁.trans h₂.symm) with he | hc
  · exact he
  · exact absurd hc (heapOpenColl_refutable_of_injective S8 hCR _ _ _)

/-- **THE GENTIAN CLOSE AT A COMMON ROOT, UNCONDITIONAL.** The `root`-shaped restatement of
`heapOpen8_binds_leaf_or_collides` — the form the membership consumers actually use: two leaves
recomposing to the SAME published root along the same path are the same leaf, or the named collision. -/
theorem membersAt8_functional_on_path_or_collides
    (root : Digest8) {e₁ e₂ : ℤ × ℤ × ℤ}
    (path : List (CapMerkleGeneric.StepG Digest8))
    (h₁ : recomposeUp8 S8 (heapLeafDigest8 S8 e₁) path = root)
    (h₂ : recomposeUp8 S8 (heapLeafDigest8 S8 e₂) path = root) :
    e₁ = e₂ ∨ HeapOpenColl S8 e₁ e₂ path :=
  heapOpen8_binds_leaf_or_collides S8 path (h₁.trans h₂.symm)

end Heap8Scheme

/-! ### §H.D — ⚑ THE ACCEPTANCE TEST: a REAL DEPLOYED `Heap8Scheme` VALUE.

The whole point of deleting the `chip8CR` field is measured HERE, not by a green build. With the field
present, `Heap8Scheme` had no deployed inhabitant (`VacuitySweepTeeth.compress8CR_false_babyBear` refutes
the field for any function landing in bounded BabyBear lanes, which the deployed chip does), so every
`∀ S8 : Heap8Scheme, …` theorem — the entire heap-open surface, and with it the sorted-tree forcing the
perimeter leans on — was vacuously true.

`deployedHeap8Scheme` below is a VALUE, and it rides the SAME `deployedShapedChip8` the cap inhabitant
does — which is not a shortcut but the FAITHFUL modelling choice: one `node8` chip
(`descriptor_ir2::chip_absorb_all_lanes` at arity 16) serves cap, heap, AND fields in the deployment.
Its chip squeezes an arbitrary-length `List ℤ` into eight lanes each reduced into `[0, p)` for the
deployed BabyBear prime, and decisively its own chip REFUTES the deleted field
(`VacuitySweepTeeth.deployedHeap8Scheme_chip_not_Compress8CR`). That is the tightest statement of what
changed: **the very function the teeth refute now INHABITS the structure.**

⚑ Honest scope: this is not a KAT-faithful Poseidon2 model (none exists in Lean here), so it is not a
byte-differential against the Rust chip. It is a deployed-SHAPED inhabitant, and shape is precisely what
the vacuity argument was about. -/

/-- ⚑ **THE CONSTRUCTED INHABITANT — a real deployed `Heap8Scheme` VALUE.** This term is what the old
structure could not have. Every theorem in §H.X now has an instance to be applied at. -/
def deployedHeap8Scheme : Heap8Scheme := ⟨deployedShapedChip8⟩

/-- The inhabitant's chip IS the deployed-shaped chip (definitional — the projection fires). -/
theorem deployedHeap8Scheme_chip : deployedHeap8Scheme.chipAbsorb8 = deployedShapedChip8 := rfl

/-- ⚑ **THE TOOTH FIRES AT THE INHABITANT.** The heap-open GENTIAN close, INSTANTIATED at a real value —
the operation the `∀ S8 : Heap8Scheme` form could never actually be performed for. -/
theorem deployed_heapOpen8_binds_leaf_or_collides
    (path : List (CapMerkleGeneric.StepG Digest8)) {e₁ e₂ : ℤ × ℤ × ℤ}
    (h : Heap8Scheme.recomposeUp8 deployedHeap8Scheme
           (Heap8Scheme.heapLeafDigest8 deployedHeap8Scheme e₁) path
       = Heap8Scheme.recomposeUp8 deployedHeap8Scheme
           (Heap8Scheme.heapLeafDigest8 deployedHeap8Scheme e₂) path) :
    e₁ = e₂ ∨ Heap8Scheme.HeapOpenColl deployedHeap8Scheme e₁ e₂ path :=
  Heap8Scheme.heapOpen8_binds_leaf_or_collides deployedHeap8Scheme path h

/-! #### §H.D-guards — the inhabitant RUNS (computable witnesses, no `native_decide`). -/

/-- A concrete LINKED IMT heap leaf `(addr, value, nextAddr)`. -/
def demoHeapLeaf8A : ℤ × ℤ × ℤ := (11, 22, 33)

/-- The SAME address and pointer with a different VALUE — the balance mutation. -/
def demoHeapLeaf8B : ℤ × ℤ × ℤ := (11, 99, 33)

/-- The SAME `(addr, value)` with a RELINKED pointer — the gap-#5 IMT mutation the 1-felt commitment
was blind to and the 3-field leaf digest is supposed to bind. -/
def demoHeapLeaf8C : ℤ × ℤ × ℤ := (11, 22, 44)

/-- A concrete two-level sibling/direction path. -/
def demoHeapPath8 : List (CapMerkleGeneric.StepG Digest8) :=
  [⟨fun _ => 101, false⟩, ⟨fun _ => 202, true⟩]

-- The deployed inhabitant's heap-leaf digest is a genuine 8-lane vector.
#guard (List.ofFn (Heap8Scheme.heapLeafDigest8 deployedHeap8Scheme demoHeapLeaf8A)).length == 8

-- Every lane lands inside the BabyBear range.
#guard (List.ofFn (Heap8Scheme.heapLeafDigest8 deployedHeap8Scheme demoHeapLeaf8A)).all
    (fun x => 0 ≤ x && x < BABYBEAR_P)

-- NON-VACUITY, at the inhabitant: flipping the VALUE moves the 8-felt leaf digest.
#guard (List.ofFn (Heap8Scheme.heapLeafDigest8 deployedHeap8Scheme demoHeapLeaf8A))
    != (List.ofFn (Heap8Scheme.heapLeafDigest8 deployedHeap8Scheme demoHeapLeaf8B))

-- ... and RELINKING the sorted-chain POINTER alone moves it too: the IMT link is genuinely IN the
-- digest, so the chain cannot be rewired under a fixed `(addr, value)`.
#guard (List.ofFn (Heap8Scheme.heapLeafDigest8 deployedHeap8Scheme demoHeapLeaf8A))
    != (List.ofFn (Heap8Scheme.heapLeafDigest8 deployedHeap8Scheme demoHeapLeaf8C))

-- ... and the value mutation MOVES the recomposed 8-felt heap ROOT along a real two-level path: the
-- whole `node8` membership machinery COMPUTES on the constructed value.
#guard (List.ofFn (Heap8Scheme.recomposeUp8 deployedHeap8Scheme
        (Heap8Scheme.heapLeafDigest8 deployedHeap8Scheme demoHeapLeaf8A) demoHeapPath8))
    != (List.ofFn (Heap8Scheme.recomposeUp8 deployedHeap8Scheme
        (Heap8Scheme.heapLeafDigest8 deployedHeap8Scheme demoHeapLeaf8B) demoHeapPath8))

/-! ### §H.R — the REFUTABILITY reference chips (both branches are REACHABLE across schemes).

`Compress8CR` is no longer a field, so an injective toy chip is no longer offered as a "non-vacuity"
argument (that was the FALSE COMFORT: toy witness satisfiable, real compressing Poseidon2 false). What
these are FOR now is making §H.S's canaries CONCRETE — at `refHeapScheme8` the collision disjunct is
genuinely unavailable, and at `badHeapScheme8` it is genuinely INHABITED. -/

namespace Reference8

open Dregg2.Circuit.DeployedCapTree.Reference8 (refChipAbsorb8 refChip8CR badChipAbsorb8)

/-- The reference 8-felt heap scheme, on the cap tree's injective toy chip (no CR field to supply). -/
def refHeapScheme8 : Heap8Scheme := ⟨refChipAbsorb8⟩

/-- **THE CANARY, CONCRETE: at this chip NO extracted pair is a collision.** So
`heapOpen8_binds_leaf_or_collides` cannot discharge itself on the right — the binding half does the
work, and the disjunction carries strictly more than `True`. -/
theorem refHeapScheme8_heapOpenColl_refutable (e₁ e₂ : ℤ × ℤ × ℤ)
    (path : List (CapMerkleGeneric.StepG Digest8)) :
    ¬ Heap8Scheme.HeapOpenColl refHeapScheme8 e₁ e₂ path :=
  Heap8Scheme.heapOpenColl_refutable_of_injective refHeapScheme8 refChip8CR e₁ e₂ path

/-- **AND THE OLD CONCLUSION IS RECOVERED THERE.** At the injective reference chip the deleted GENTIAN
close falls straight out of the new disjunction. -/
theorem refHeapScheme8_gentian_close (root : Digest8) {e₁ e₂ : ℤ × ℤ × ℤ}
    (path : List (CapMerkleGeneric.StepG Digest8))
    (h₁ : Heap8Scheme.recomposeUp8 refHeapScheme8
            (Heap8Scheme.heapLeafDigest8 refHeapScheme8 e₁) path = root)
    (h₂ : Heap8Scheme.recomposeUp8 refHeapScheme8
            (Heap8Scheme.heapLeafDigest8 refHeapScheme8 e₂) path = root) : e₁ = e₂ :=
  Heap8Scheme.membersAt8_functional_on_path_of_injective refHeapScheme8 refChip8CR root path h₁ h₂

/-- The colliding chip is a `Heap8Scheme` too — and at it the `Coll8` disjunct is genuinely INHABITED,
so the two branches of every `…_or_collides` theorem are BOTH reachable across schemes. -/
def badHeapScheme8 : Heap8Scheme := ⟨badChipAbsorb8⟩

theorem badHeapScheme8_has_coll8 : Coll8 badHeapScheme8.chipAbsorb8 ([0], [1]) :=
  ⟨by simp, rfl⟩

end Reference8

/-! ### §H.ROM — ⚑ THE ROM SUCCESSORS: the heap-tree binding surface as REDUCTIONS on the PROVED
keyed floor.

⚑ STATUS OF THE `…_binds_or_collides` FAMILY (2026-07-24). The §H.X disjunctions are EXTRACTOR
MACHINERY (each hands back the specific colliding pair its reduction consumes), but as EXPORTED
security statements they are shirks: at deployed BabyBear parameters a collision EXISTS by
pigeonhole, so each disjunction holds through its right branch with NO binding. The security
statements are THIS section's `…_binds_rom` reductions on `Crypto.RomHashedLeafOpening`'s kit —
forger an ORACLE PROGRAM fixed before the oracle is sampled, closed from `keyedRom_hard` (the
birthday bound, a THEOREM), queries PAID, no refuted floor. The disjunctions are RETAINED for
their downstream `rcases` consumers (`VacuitySweepTeeth`, `MapMerkleRoot`,
`Emit.HeapLeafWideEmit`, `Emit.EffectVmEmitRotationV3`, `RotatedKernelRefinementCapFamily`,
`Deos.DocSubstrateSound`), whose re-point is the remaining mechanical work. The modelling step is
the cap tree's §7R note verbatim. -/

section RomSuccessor

open Dregg2.Crypto.RomHashedLeafOpening
open Dregg2.Crypto.RomBindingReduction (RomCarrier romCarrierGame RomCarrierEff)
open Dregg2.Crypto.RomCarrierSites (RomForgeryEff)
open Dregg2.Crypto.FloorGames (Adversary gameAdv)
open Dregg2.Crypto.ConcreteSecurity (Negl PolyBounded)
open Dregg2.Circuit.DeployedCapTree (feltTrunc feltTrunc_inj)

/-- The truncated LINKED IMT heap-leaf block `(addr, value, nextAddr)` at the deployed BabyBear
range (`heap_root.rs::HeapLeaf::digest8`'s 3-limb absorb). -/
abbrev HeapLeafRomBlock : Type :=
  Fin Dregg2.Crypto.RomCarrierSites.babyBearP × Fin Dregg2.Crypto.RomCarrierSites.babyBearP
    × Fin Dregg2.Crypto.RomCarrierSites.babyBearP

/-- **THE HEAP-TREE ROM FAMILY** at tag space `Key`: truncated 3-limb IMT leaf blocks ⊕ ordered
ideal-digest node pairs (the deployed 3-vs-16 arity separation, by constructor). -/
abbrev heapRomFamily (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key)
    (kN : Nonempty Key) : Dregg2.Crypto.KeyedRomFloor.KeyedRomFamily :=
  hlFam Key kF kD kN (fun _ => HeapLeafRomBlock) (fun _ => inferInstance)
    (fun _ => inferInstance)

/-- The heap-leaf carrier — the leaf digest binds the WHOLE linked triple (addr, value, and the
IMT pointer the 1-felt commitment was blind to). -/
abbrev heapLeafRomCarrier (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key)
    (kN : Nonempty Key) : RomCarrier (heapRomFamily Key kF kD kN) :=
  hlLeafCarrier Key kF kD kN (fun _ => HeapLeafRomBlock) (fun _ => inferInstance)
    (fun _ => inferInstance)

/-- The heap-node carrier — the `node8` digest binds BOTH ordered children. -/
abbrev heapNodeRomCarrier (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key)
    (kN : Nonempty Key) : RomCarrier (heapRomFamily Key kF kD kN) :=
  hlNodeCarrier Key kF kD kN (fun _ => HeapLeafRomBlock) (fun _ => inferInstance)
    (fun _ => inferInstance)

/-- **⚑⚑ THE HEAP-LEAF BINDING, AS A REDUCTION** — ROM successor of
`heapLeafDigest8_binds_or_collides`'s left disjunct. -/
theorem heapLeafDigest8_binds_rom (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key)
    (kN : Nonempty Key) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (romCarrierGame (heapRomFamily Key kF kD kN)
      (heapLeafRomCarrier Key kF kD kN)))
    (hA : RomCarrierEff (heapRomFamily Key kF kD kN) (heapLeafRomCarrier Key kF kD kN) Q A) :
    Negl (gameAdv (romCarrierGame (heapRomFamily Key kF kD kN)
      (heapLeafRomCarrier Key kF kD kN)) A) :=
  hlLeaf_binds_rom Key kF kD kN _ _ _ Q hQ A hA

/-- **⚑⚑ THE HEAP-NODE BINDING, AS A REDUCTION** — ROM successor of
`heapNodeOf8_binds_or_collides`'s left disjunct. -/
theorem heapNodeOf8_binds_rom (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key)
    (kN : Nonempty Key) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (romCarrierGame (heapRomFamily Key kF kD kN)
      (heapNodeRomCarrier Key kF kD kN)))
    (hA : RomCarrierEff (heapRomFamily Key kF kD kN) (heapNodeRomCarrier Key kF kD kN) Q A) :
    Negl (gameAdv (romCarrierGame (heapRomFamily Key kF kD kN)
      (heapNodeRomCarrier Key kF kD kN)) A) :=
  hlNode_binds_rom Key kF kD kN _ _ _ Q hQ A hA

/-- **⚑⚑ THE HEAP SPINE BINDING, AS A REDUCTION** — ROM successor of
`recomposeUp8_binds_or_collides`. -/
theorem heapRecomposeUp8_binds_rom (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key)
    (kN : Nonempty Key) (dep Q Q' : ℕ → ℕ)
    (hle : ∀ l, Q l + 2 * dep l ≤ Q' l)
    (hQ' : PolyBounded (fun l => ((Q' l : ℝ) * (Q' l : ℝ) + 1)))
    (A : Adversary (hlPathForgery Key kF kD kN (fun _ => HeapLeafRomBlock)
      (fun _ => inferInstance) (fun _ => inferInstance) dep).game)
    (hA : RomForgeryEff (heapRomFamily Key kF kD kN)
      (hlPathForgery Key kF kD kN (fun _ => HeapLeafRomBlock)
        (fun _ => inferInstance) (fun _ => inferInstance) dep) Q A) :
    Negl (gameAdv (hlPathForgery Key kF kD kN (fun _ => HeapLeafRomBlock)
      (fun _ => inferInstance) (fun _ => inferInstance) dep).game A) :=
  hlPathRom_binds Key kF kD kN _ _ _ dep Q Q' hle hQ' A hA

/-- **⚑⚑ THE HEAP GENTIAN CLOSE, AS A REDUCTION** — ROM successor of
`heapOpen8_binds_leaf_or_collides` (and of its deployed instantiation
`deployed_heapOpen8_binds_leaf_or_collides` — the ROM statement is about the SAMPLED oracle, so
the ∀-scheme and at-the-inhabitant forms collapse into one). -/
theorem heapOpen8_binds_leaf_rom (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key)
    (kN : Nonempty Key) (dep Q Q' : ℕ → ℕ)
    (hle : ∀ l, Q l + (2 * dep l + 2) ≤ Q' l)
    (hQ' : PolyBounded (fun l => ((Q' l : ℝ) * (Q' l : ℝ) + 1)))
    (A : Adversary (hlOpenForgery Key kF kD kN (fun _ => HeapLeafRomBlock)
      (fun _ => inferInstance) (fun _ => inferInstance) dep).game)
    (hA : RomForgeryEff (heapRomFamily Key kF kD kN)
      (hlOpenForgery Key kF kD kN (fun _ => HeapLeafRomBlock)
        (fun _ => inferInstance) (fun _ => inferInstance) dep) Q A) :
    Negl (gameAdv (hlOpenForgery Key kF kD kN (fun _ => HeapLeafRomBlock)
      (fun _ => inferInstance) (fun _ => inferInstance) dep).game A) :=
  hlOpenRom_binds Key kF kD kN _ _ _ dep Q Q' hle hQ' A hA

/-- **⚑ THE PUBLISHED-ROOT FORM** — ROM successor of
`membersAt8_functional_on_path_or_collides`: two query-bounded openings of ONE published heap root
to two DISTINCT linked leaves succeed with negligible probability. -/
theorem heapMembersAt8_functional_rom (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key)
    (kN : Nonempty Key) (dep Q Q' : ℕ → ℕ)
    (hle : ∀ l, Q l + (2 * dep l + 2) ≤ Q' l)
    (hQ' : PolyBounded (fun l => ((Q' l : ℝ) * (Q' l : ℝ) + 1)))
    (A : Adversary (hlOpenRootForgery Key kF kD kN (fun _ => HeapLeafRomBlock)
      (fun _ => inferInstance) (fun _ => inferInstance) dep).game)
    (hA : RomForgeryEff (heapRomFamily Key kF kD kN)
      (hlOpenRootForgery Key kF kD kN (fun _ => HeapLeafRomBlock)
        (fun _ => inferInstance) (fun _ => inferInstance) dep) Q A) :
    Negl (gameAdv (hlOpenRootForgery Key kF kD kN (fun _ => HeapLeafRomBlock)
      (fun _ => inferInstance) (fun _ => inferInstance) dep).game A) :=
  hlOpenRootRom_binds Key kF kD kN _ _ _ dep Q Q' hle hQ' A hA

/-- The truncation pin: a range-bounded deployed IMT triple embeds LOSSLESSLY into the ROM block. -/
def heapLeafRomBlockOf (e : ℤ × ℤ × ℤ) : HeapLeafRomBlock :=
  (feltTrunc e.1, feltTrunc e.2.1, feltTrunc e.2.2)

theorem heapLeafRomBlockOf_inj {e₁ e₂ : ℤ × ℤ × ℤ}
    (h₁ : ∀ x ∈ [e₁.1, e₁.2.1, e₁.2.2], 0 ≤ x ∧ x < BABYBEAR_P)
    (h₂ : ∀ x ∈ [e₂.1, e₂.2.1, e₂.2.2], 0 ≤ x ∧ x < BABYBEAR_P)
    (h : heapLeafRomBlockOf e₁ = heapLeafRomBlockOf e₂) : e₁ = e₂ := by
  obtain ⟨ha0, ha1⟩ := h₁ e₁.1 (by simp)
  obtain ⟨hb0, hb1⟩ := h₁ e₁.2.1 (by simp)
  obtain ⟨hc0, hc1⟩ := h₁ e₁.2.2 (by simp)
  obtain ⟨hd0, hd1⟩ := h₂ e₂.1 (by simp)
  obtain ⟨he0, he1⟩ := h₂ e₂.2.1 (by simp)
  obtain ⟨hf0, hf1⟩ := h₂ e₂.2.2 (by simp)
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact feltTrunc_inj ha0 ha1 hd0 hd1 (congrArg Prod.fst h)
  · exact feltTrunc_inj hb0 hb1 he0 he1 (congrArg (fun p => p.2.1) h)
  · exact feltTrunc_inj hc0 hc1 hf0 hf1 (congrArg (fun p => p.2.2) h)

/-- The deployed single-tag instantiation elaborates (`Key := Unit`) — the inhabitation tooth. -/
theorem deployedShape_heapOpen8_binds_leaf_rom (dep Q Q' : ℕ → ℕ)
    (hle : ∀ l, Q l + (2 * dep l + 2) ≤ Q' l)
    (hQ' : PolyBounded (fun l => ((Q' l : ℝ) * (Q' l : ℝ) + 1)))
    (A : Adversary (hlOpenForgery Unit inferInstance inferInstance inferInstance
      (fun _ => HeapLeafRomBlock) (fun _ => inferInstance) (fun _ => inferInstance) dep).game)
    (hA : RomForgeryEff (heapRomFamily Unit inferInstance inferInstance inferInstance)
      (hlOpenForgery Unit inferInstance inferInstance inferInstance
        (fun _ => HeapLeafRomBlock) (fun _ => inferInstance) (fun _ => inferInstance) dep)
      Q A) :
    Negl (gameAdv (hlOpenForgery Unit inferInstance inferInstance inferInstance
      (fun _ => HeapLeafRomBlock) (fun _ => inferInstance) (fun _ => inferInstance) dep).game
      A) :=
  heapOpen8_binds_leaf_rom Unit inferInstance inferInstance inferInstance dep Q Q' hle hQ' A hA

end RomSuccessor

/-! ### §H.A — Axiom hygiene. -/
-- §H.ROM — the ROM successors (reductions on the proved keyed floor; no bare disjunction).
#assert_axioms heapLeafDigest8_binds_rom
#assert_axioms heapNodeOf8_binds_rom
#assert_axioms heapRecomposeUp8_binds_rom
#assert_axioms heapOpen8_binds_leaf_rom
#assert_axioms heapMembersAt8_functional_rom
#assert_axioms heapLeafRomBlockOf_inj
#assert_axioms deployedShape_heapOpen8_binds_leaf_rom

#assert_axioms Heap8Scheme.heapLeafBlock_inj
#assert_axioms Heap8Scheme.heapLeafDigest8_binds_or_collides
#assert_axioms Heap8Scheme.heapNodeOf8_binds_or_collides
#assert_axioms Heap8Scheme.recomposeUp8_binds_or_collides
#assert_axioms Heap8Scheme.heapOpen8_binds_leaf_or_collides
#assert_axioms Heap8Scheme.membersAt8_functional_on_path_or_collides
#assert_axioms Heap8Scheme.heapOpenColl_refutable_of_injective
#assert_axioms Heap8Scheme.heapLeafDigest8_injective_of_injective
#assert_axioms Heap8Scheme.heapNodeOf8_injective_of_injective
#assert_axioms Heap8Scheme.recomposeUp8_inj_of_path_of_injective
#assert_axioms Heap8Scheme.membersAt8_functional_on_path_of_injective
#assert_axioms deployedHeap8Scheme_chip
#assert_axioms deployed_heapOpen8_binds_leaf_or_collides
#assert_axioms Reference8.refHeapScheme8_heapOpenColl_refutable
#assert_axioms Reference8.refHeapScheme8_gentian_close
#assert_axioms Reference8.badHeapScheme8_has_coll8

end Dregg2.Circuit.DeployedHeapTree

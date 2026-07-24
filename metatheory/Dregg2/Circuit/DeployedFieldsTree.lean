import Dregg2.Circuit.DeployedCapTree
import Dregg2.Circuit.CapMerkleGeneric

/-!
# `DeployedFieldsTree` — the native 8-felt user-field-MAP tree spine (Phase H-FIELDS-8).

The THIRD and LAST faithful root's Lean spine, the exact twin of `DeployedHeapTree`'s `Heap8Scheme`
(and of `DeployedCapTree`'s `Cap8Scheme`). The deployed fields tree is a sorted-Poseidon2 binary
Merkle map over LINKED IMT leaves `(addr, value, nextAddr)` (`addr = openable_fields_root::
field_key_hash key`, `value = fold_bytes32 v`, `nextAddr` = the gap-#5 IMT pointer to the next-larger
present address) — the SAME `HeapLeaf` / `node8` scheme `heap_root.rs::compute_canonical_heap_root_8`
folds, over the `fields_root_leaves` set. The historical commitment projected each node/leaf to a SINGLE
felt (`hash : List ℤ → ℤ`, ~2^31), well below the deployed FRI/STARK ~124-bit soundness floor: two
genuinely-different field maps can collide on the 1-felt root while topping different 8-felt roots (the
fields GENTIAN tooth `circuit/tests/fields_root_gentian_weld.rs` exhibits a concrete pair). This module
gives the FAITHFUL 8-felt fields tree — every node absorbs full 8-felt children through the arity-16
`node8` chip and emits a full 8-felt digest.

⚑ **THE `chip8CR` FIELD IS GONE (2026-07-20), AND THE STRUCTURE IS NOW INHABITED.** `Fields8Scheme` used
to carry `chip8CR : Compress8CR chipAbsorb8` as a FIELD — injectivity of a map that squeezes the
infinite `List ℤ` into 8 bounded BabyBear lanes. `VacuitySweepTeeth.compress8CR_false_babyBear` refutes
that for ANY function of that shape, the deployed chip included, so NO deployed `Fields8Scheme` value
could be constructed and every theorem of the form `∀ S8 : Fields8Scheme, …` was VACUOUS. §F.D below
exhibits `deployedFields8Scheme`, a real value whose OWN chip the teeth refute. The binding the tree
used to ASSUME is now EXTRACTED AS DATA: see `DeployedCapTree.Coll8` and the `…_binds_or_collides`
family.

REUSE (the Option-A payoff, exactly as for cap and heap): the membership-recompose anti-ghost spine is
digest-type-AGNOSTIC and already proved once — `CapMerkleGeneric.recomposeGFind`/`recomposeGFind_spec`,
the TOTAL-FUNCTION peel — so the fields tree instantiates it rather than re-authoring a parallel copy.
`Digest8`, `Compress8CR`, `Coll8`, and `pack8`/`pack8_inj` are shared verbatim from `DeployedCapTree` —
cap/heap/fields all ride the ONE `node8` compression (`descriptor_ir2::chip_absorb_all_lanes` at
`CHIP_NODE8_ARITY = 16`), which is also why §F.D's inhabitant rides the SAME deployed-shaped chip the
cap and heap inhabitants do.
-/

namespace Dregg2.Circuit.DeployedFieldsTree

open Dregg2.Circuit.DeployedCapTree (Digest8 Compress8CR Coll8 BABYBEAR_P deployedShapedChip8)
open Dregg2.Circuit.DeployedCapTree.Cap8Scheme (pack8 pack8_inj coll8_refutable_of_injective)

/-- **`Fields8Scheme`** — the native-8-felt fields-tree's SINGLE Poseidon2 carrier: the 8-output chip
absorb `chipAbsorb8 : List ℤ → Digest8` (`descriptor_ir2::chip_absorb_all_lanes`, all 8 squeezed
lanes). BOTH the leaf (`fieldsLeafDigest8`, arity 3 — the IMT `[addr, value, nextAddr]`) and the node
(`fieldsNodeOf8`, arity 16) ride it; the input lists are length-disjoint (3 vs 16), so the chip's
per-row `(arity, padded inputs)` seeding separates the two domains for free. The exact twin of
`DeployedHeapTree.Heap8Scheme` — indeed the SAME carrier (one `node8` chip serves cap/heap/fields).

⚑ **ONE FIELD, AND IT IS INHABITED.** The `chip8CR : Compress8CR chipAbsorb8` field is DELETED — see
this module's header for why it made the type uninhabitable, and §F.D for the real value that now
inhabits it and whose own chip refutes the deleted claim
(`VacuitySweepTeeth.deployedFields8Scheme_chip_not_Compress8CR`). -/
structure Fields8Scheme where
  /-- The single 8-output chip-absorb compression (`heap_root.rs::heap_node8`/`HeapLeaf::digest8`, the
  carrier `compute_canonical_fields_root_8` folds). -/
  chipAbsorb8 : List ℤ → Digest8

namespace Fields8Scheme

variable (S8 : Fields8Scheme)

/-- **`fieldsLeafDigest8 S8 e`** — the 8-felt deployed fields leaf digest, the SINGLE 8-output chip
absorb over the 3 LINKED-leaf fields `[addr, value, nextAddr]` (`addr = field_key_hash key`,
`value = fold_bytes32 v`, `nextAddr` = the IMT pointer). BYTE-IDENTICAL to
`heap_root.rs::HeapLeaf::digest8` (`chip_absorb_all_lanes(3, …)`) over a `fields_root_leaves` entry. -/
def fieldsLeafDigest8 (e : ℤ × ℤ × ℤ) : Digest8 := S8.chipAbsorb8 [e.1, e.2.1, e.2.2]

/-- **`fieldsNodeOf8 S8 l r`** — the native 8-felt internal node, the arity-16 chip absorb over
`pack8 l r = L8 ‖ R8`. BYTE-IDENTICAL to `heap_root.rs::heap_node8`. The SAME `chipAbsorb8` carrier as
the leaf — one fields hash everywhere. The 8-felt faithful twin of `MapMerkleRoot.mapNode`. -/
def fieldsNodeOf8 (l r : Digest8) : Digest8 := S8.chipAbsorb8 (pack8 l r)

/-- The IMT leaf block `[addr, value, nextAddr]` is injective in the triple — pure list/product
plumbing, no crypto. Factored out because BOTH the binding extractor and its strength bridge need it. -/
theorem fieldsLeafBlock_inj {e₁ e₂ : ℤ × ℤ × ℤ}
    (h : [e₁.1, e₁.2.1, e₁.2.2] = [e₂.1, e₂.2.1, e₂.2.2]) : e₁ = e₂ := by
  simp only [List.cons.injEq, and_true] at h
  exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2)

/-! ### §F.X — BINDING, EXTRACTED AS DATA (the sound replacement for the deleted injectivity family).

The four theorems this section replaces — `fieldsLeafDigest8_injective`, `fieldsNodeOf8_injective`,
`recomposeUp8_inj_of_path`, `membersAt8_functional_on_path` — were ALL discharged from the `chip8CR`
FIELD, i.e. from `Compress8CR chipAbsorb8`, which the deployed chip refutes. They are DELETED, not kept
beside the new forms: keeping them is what would make this regrounding additive and therefore inert.

Each is replaced by a TOTAL EXTRACTOR plus a theorem that what it returns is a genuine collision. The
conclusions are disjunctions `binding ∨ Coll8 chipAbsorb8 (the pair the extractor returned)`. As
FORMULAS they are weaker than the equalities they replace; as CONTENT AT DEPLOYED PARAMETERS they are
strictly stronger, because the deleted premise is unsatisfiable by the real chip — the old theorems
said nothing about the deployed system, and these hold OF it. §F.S proves that relation both ways. -/

/-- The fields-leaf extractor: the two arity-3 IMT blocks the chip absorbed. -/
def fieldsLeafColl8Find (e₁ e₂ : ℤ × ℤ × ℤ) : List ℤ × List ℤ :=
  ([e₁.1, e₁.2.1, e₁.2.2], [e₂.1, e₂.2.1, e₂.2.2])

/-- **Fields-leaf binding at 8-felt width, UNCONDITIONAL** (replaces `fieldsLeafDigest8_injective`).
Equal 8-felt leaf digests EITHER force the whole LINKED triple equal — the hashed field KEY, the folded
VALUE, AND the sorted-chain POINTER — OR the two arity-3 IMT blocks ARE a genuine collision of the
deployed chip, handed back by name. -/
theorem fieldsLeafDigest8_binds_or_collides {e₁ e₂ : ℤ × ℤ × ℤ}
    (h : fieldsLeafDigest8 S8 e₁ = fieldsLeafDigest8 S8 e₂) :
    e₁ = e₂ ∨ Coll8 S8.chipAbsorb8 (fieldsLeafColl8Find e₁ e₂) := by
  by_cases he : e₁ = e₂
  · exact Or.inl he
  · exact Or.inr ⟨fun hf => he (fieldsLeafBlock_inj hf), h⟩

/-- The fields-node extractor: the two arity-16 `L8 ‖ R8` input blocks. -/
def fieldsNodeColl8Find (l₁ r₁ l₂ r₂ : Digest8) : List ℤ × List ℤ := (pack8 l₁ r₁, pack8 l₂ r₂)

/-- **Fields-node binding at 8-felt width, UNCONDITIONAL** (replaces `fieldsNodeOf8_injective`, the
"SOLE width-specific obligation" the whole native-8-felt fields tree used to ride). Equal `node8` images
EITHER force equal 8-felt children, OR the two packed arity-16 blocks ARE a genuine chip collision. -/
theorem fieldsNodeOf8_binds_or_collides {l₁ r₁ l₂ r₂ : Digest8}
    (h : fieldsNodeOf8 S8 l₁ r₁ = fieldsNodeOf8 S8 l₂ r₂) :
    (l₁ = l₂ ∧ r₁ = r₂) ∨ Coll8 S8.chipAbsorb8 (fieldsNodeColl8Find l₁ r₁ l₂ r₂) := by
  by_cases hn : l₁ = l₂ ∧ r₁ = r₂
  · exact Or.inl hn
  · exact Or.inr ⟨fun hp => hn (pack8_inj hp), h⟩

/-- **`recomposeUp8 S8 cur path`** — the native-8-felt fields membership recompose, DEFINED as the
generic `CapMerkleGeneric.recomposeG` at `D := Digest8`, `node := fieldsNodeOf8 S8`. No bespoke
recursion — the SAME generic spine cap/heap ride. BYTE-IDENTICAL to `heap_root.rs::recompose_membership_8`
and to the deployed in-circuit `node8` MapOps chain (unified onto `BUS_P2`). -/
def recomposeUp8 (cur : Digest8) (path : List (CapMerkleGeneric.StepG Digest8)) : Digest8 :=
  CapMerkleGeneric.recomposeG (fieldsNodeOf8 S8) cur path

/-- **The native-8-felt fields spine EXTRACTOR** — the generic path walk
(`CapMerkleGeneric.recomposeGFind`) at `node := fieldsNodeOf8 S8`, with the colliding child-pairs it
lands on mapped through `pack8` into the two arity-16 chip input blocks. A TOTAL function of the two
starting digests and the path. REUSED, not re-authored: the walk is proved once, generically. -/
def recomposeUp8Find (a b : Digest8) (path : List (CapMerkleGeneric.StepG Digest8)) :
    List ℤ × List ℤ :=
  (pack8 (CapMerkleGeneric.recomposeGFind (fieldsNodeOf8 S8) a b path).1.1
         (CapMerkleGeneric.recomposeGFind (fieldsNodeOf8 S8) a b path).1.2,
   pack8 (CapMerkleGeneric.recomposeGFind (fieldsNodeOf8 S8) a b path).2.1
         (CapMerkleGeneric.recomposeGFind (fieldsNodeOf8 S8) a b path).2.2)

/-- **The native-8-felt fields anti-ghost spine, UNCONDITIONAL** (replaces `recomposeUp8_inj_of_path`).
Equal recomposed roots along a FIXED path EITHER force equal starting 8-felt digests, OR the walk LANDS
on a level whose two arity-16 `node8` blocks are a genuine chip collision, returned by name. A prover
cannot keep the published 8-felt fields root while swapping the opened leaf UNLESS the deployed chip
actually collides at the two blocks this extractor hands back.

Still a PURE RE-INSTANTIATION — `CapMerkleGeneric.recomposeGFind_spec` is proved once, generically. -/
theorem recomposeUp8_binds_or_collides (path : List (CapMerkleGeneric.StepG Digest8))
    {a b : Digest8} (h : recomposeUp8 S8 a path = recomposeUp8 S8 b path) :
    a = b ∨ Coll8 S8.chipAbsorb8 (recomposeUp8Find S8 a b path) := by
  rcases CapMerkleGeneric.recomposeGFind_spec (fieldsNodeOf8 S8) path h with heq | ⟨hne, himg⟩
  · exact Or.inl heq
  · refine Or.inr ⟨fun hp => hne ?_, himg⟩
    exact Prod.ext (pack8_inj hp).1 (pack8_inj hp).2

/-- **THE FIELDS-OPEN EXTRACTOR** — the SINGLE named pair the whole fields-open peel hands back. Run the
spine walk over the two leaf digests; if it found a genuine collision that is the answer, otherwise the
walk has already forced the two leaf DIGESTS equal, so the collision (if any) is at the leaf absorb and
the two arity-3 IMT blocks are the pair. -/
def fieldsOpen8Find (e₁ e₂ : ℤ × ℤ × ℤ) (path : List (CapMerkleGeneric.StepG Digest8)) :
    List ℤ × List ℤ :=
  if Coll8 S8.chipAbsorb8
      (recomposeUp8Find S8 (fieldsLeafDigest8 S8 e₁) (fieldsLeafDigest8 S8 e₂) path)
  then recomposeUp8Find S8 (fieldsLeafDigest8 S8 e₁) (fieldsLeafDigest8 S8 e₂) path
  else fieldsLeafColl8Find e₁ e₂

/-- **`FieldsOpenColl S8 e₁ e₂ path`** — the pair `fieldsOpen8Find` RETURNS on this equivocation is a
genuine collision of the deployed arity-16 chip. The ONE named disjunct every fields-open consumer
carries in place of the deleted `chip8CR` floor. -/
def FieldsOpenColl (e₁ e₂ : ℤ × ℤ × ℤ) (path : List (CapMerkleGeneric.StepG Digest8)) : Prop :=
  Coll8 S8.chipAbsorb8 (fieldsOpen8Find S8 e₁ e₂ path)

/-- **⚑ THE GENTIAN CLOSE, UNCONDITIONAL** (replaces `membersAt8_functional_on_path`). Two LINKED field
leaves opening the SAME 8-felt root along the SAME committed path are EITHER the same leaf (key, value,
AND pointer), OR the deployed chip genuinely collides at the two blocks `fieldsOpen8Find` hands back.

This is what the 8-felt migration actually buys, stated honestly: the lane-0 forge the GENTIAN tooth
exhibits (`circuit/tests/fields_root_gentian_weld.rs` — different entries, same 1-felt projection) is
excluded UNLESS the adversary produces a full ~124-bit collision at a NAMED pair of arity-16 blocks. The
old form asserted the exclusion outright while resting on a premise the deployed chip refutes. -/
theorem fieldsOpen8_binds_leaf_or_collides (path : List (CapMerkleGeneric.StepG Digest8))
    {e₁ e₂ : ℤ × ℤ × ℤ}
    (h : recomposeUp8 S8 (fieldsLeafDigest8 S8 e₁) path
       = recomposeUp8 S8 (fieldsLeafDigest8 S8 e₂) path) :
    e₁ = e₂ ∨ FieldsOpenColl S8 e₁ e₂ path := by
  by_cases hif : Coll8 S8.chipAbsorb8
      (recomposeUp8Find S8 (fieldsLeafDigest8 S8 e₁) (fieldsLeafDigest8 S8 e₂) path)
  · refine Or.inr ?_
    show Coll8 S8.chipAbsorb8 (fieldsOpen8Find S8 e₁ e₂ path)
    rw [fieldsOpen8Find, if_pos hif]
    exact hif
  · rcases recomposeUp8_binds_or_collides S8 path h with hdig | hc
    · rcases fieldsLeafDigest8_binds_or_collides S8 hdig with he | hec
      · exact Or.inl he
      · refine Or.inr ?_
        show Coll8 S8.chipAbsorb8 (fieldsOpen8Find S8 e₁ e₂ path)
        rw [fieldsOpen8Find, if_neg hif]
        exact hec
    · exact absurd hc hif

/-- **`MembersAt8 S8 root e`** — the native-8-felt deployed fields-tree membership of a `(addr, value)`
PAIR: SOME linked leaf `(addr, value, next)` opens against the FULL 8-felt `root` (the IMT pointer is
existential at the map level). The HONEST 8-felt replacement for the lossy 1-felt opening — opens
against ~124-bit of root, not lane-0. The fields twin of `DeployedHeapTree.Heap8Scheme.MembersAt8`. -/
def MembersAt8 (root : Digest8) (e : ℤ × ℤ) : Prop :=
  ∃ (next : ℤ) (path : List (CapMerkleGeneric.StepG Digest8)),
    recomposeUp8 S8 (fieldsLeafDigest8 S8 (e.1, e.2, next)) path = root

/-! ### §F.S — THE STRENGTH RELATION, both directions (no strength lost; no free pass gained).

Deleting a carrier and restating its consumers as disjunctions invites two fair objections, both
answered here in Lean rather than in prose.

1. *"You weakened the theorems to make the deletion easy."* — the `…_of_injective` bridges assume
   exactly the injectivity the deleted field asserted, and each deleted theorem falls straight out.
   They are precisely the injective special case of the new ones.
2. *"The right disjunct is a free pass, so the disjunction says nothing."* —
   `fieldsOpenColl_refutable_of_injective` shows the collision disjunct is REFUTABLE: at an injective
   chip the extracted pair is NOT a collision, so the binding half has to do the work.

These are STANDALONE bridges, deliberately NOT hypotheses on any deployed keystone: `Compress8CR` is
FALSE at deployed BabyBear parameters, so a keystone carrying it would be right back where this repair
started. (The refutability core `coll8_refutable_of_injective` is shared verbatim from the cap tree —
`Coll8` is one predicate, not three.) -/

/-- **(CANARY at the fields-open composite.)** `FieldsOpenColl` is refutable at an injective chip. -/
theorem fieldsOpenColl_refutable_of_injective (hCR : Compress8CR S8.chipAbsorb8)
    (e₁ e₂ : ℤ × ℤ × ℤ) (path : List (CapMerkleGeneric.StepG Digest8)) :
    ¬ FieldsOpenColl S8 e₁ e₂ path :=
  coll8_refutable_of_injective hCR _

/-- **NO STRENGTH LOST — the deleted `fieldsLeafDigest8_injective` is the injective special case.** -/
theorem fieldsLeafDigest8_injective_of_injective (hCR : Compress8CR S8.chipAbsorb8)
    {e₁ e₂ : ℤ × ℤ × ℤ} (h : fieldsLeafDigest8 S8 e₁ = fieldsLeafDigest8 S8 e₂) : e₁ = e₂ := by
  rcases fieldsLeafDigest8_binds_or_collides S8 h with he | hc
  · exact he
  · exact absurd hc (coll8_refutable_of_injective hCR _)

/-- **NO STRENGTH LOST — the deleted `fieldsNodeOf8_injective` is the injective special case.** -/
theorem fieldsNodeOf8_injective_of_injective (hCR : Compress8CR S8.chipAbsorb8)
    {l₁ r₁ l₂ r₂ : Digest8} (h : fieldsNodeOf8 S8 l₁ r₁ = fieldsNodeOf8 S8 l₂ r₂) :
    l₁ = l₂ ∧ r₁ = r₂ := by
  rcases fieldsNodeOf8_binds_or_collides S8 h with hn | hc
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
close) is the injective special case of `fieldsOpen8_binds_leaf_or_collides`. -/
theorem membersAt8_functional_on_path_of_injective (hCR : Compress8CR S8.chipAbsorb8)
    (root : Digest8) {e₁ e₂ : ℤ × ℤ × ℤ}
    (path : List (CapMerkleGeneric.StepG Digest8))
    (h₁ : recomposeUp8 S8 (fieldsLeafDigest8 S8 e₁) path = root)
    (h₂ : recomposeUp8 S8 (fieldsLeafDigest8 S8 e₂) path = root) : e₁ = e₂ := by
  rcases fieldsOpen8_binds_leaf_or_collides S8 path (h₁.trans h₂.symm) with he | hc
  · exact he
  · exact absurd hc (fieldsOpenColl_refutable_of_injective S8 hCR _ _ _)

/-- **THE GENTIAN CLOSE AT A COMMON ROOT, UNCONDITIONAL.** The `root`-shaped restatement of
`fieldsOpen8_binds_leaf_or_collides` — the form the membership consumers actually use: two leaves
recomposing to the SAME published root along the same path are the same leaf, or the named collision. -/
theorem membersAt8_functional_on_path_or_collides
    (root : Digest8) {e₁ e₂ : ℤ × ℤ × ℤ}
    (path : List (CapMerkleGeneric.StepG Digest8))
    (h₁ : recomposeUp8 S8 (fieldsLeafDigest8 S8 e₁) path = root)
    (h₂ : recomposeUp8 S8 (fieldsLeafDigest8 S8 e₂) path = root) :
    e₁ = e₂ ∨ FieldsOpenColl S8 e₁ e₂ path :=
  fieldsOpen8_binds_leaf_or_collides S8 path (h₁.trans h₂.symm)

end Fields8Scheme

/-! ### §F.D — ⚑ THE ACCEPTANCE TEST: a REAL DEPLOYED `Fields8Scheme` VALUE.

The whole point of deleting the `chip8CR` field is measured HERE, not by a green build. With the field
present, `Fields8Scheme` had no deployed inhabitant (`VacuitySweepTeeth.compress8CR_false_babyBear`
refutes the field for any function landing in bounded BabyBear lanes, which the deployed chip does), so
every `∀ S8 : Fields8Scheme, …` theorem — the entire fields-open surface — was vacuously true.

`deployedFields8Scheme` below is a VALUE, and it rides the SAME `deployedShapedChip8` the cap and heap
inhabitants do — which is not a shortcut but the FAITHFUL modelling choice: one `node8` chip
(`descriptor_ir2::chip_absorb_all_lanes` at arity 16) serves cap, heap, AND fields in the deployment.
Its chip squeezes an arbitrary-length `List ℤ` into eight lanes each reduced into `[0, p)` for the
deployed BabyBear prime, and decisively its own chip REFUTES the deleted field
(`VacuitySweepTeeth.deployedFields8Scheme_chip_not_Compress8CR`). That is the tightest statement of what
changed: **the very function the teeth refute now INHABITS the structure.**

⚑ Honest scope: this is not a KAT-faithful Poseidon2 model (none exists in Lean here), so it is not a
byte-differential against the Rust chip. It is a deployed-SHAPED inhabitant, and shape is precisely what
the vacuity argument was about. -/

/-- ⚑ **THE CONSTRUCTED INHABITANT — a real deployed `Fields8Scheme` VALUE.** This term is what the old
structure could not have. Every theorem in §F.X now has an instance to be applied at. -/
def deployedFields8Scheme : Fields8Scheme := ⟨deployedShapedChip8⟩

/-- The inhabitant's chip IS the deployed-shaped chip (definitional — the projection fires). -/
theorem deployedFields8Scheme_chip : deployedFields8Scheme.chipAbsorb8 = deployedShapedChip8 := rfl

/-- ⚑ **THE TOOTH FIRES AT THE INHABITANT.** The fields-open GENTIAN close, INSTANTIATED at a real
value — the operation the `∀ S8 : Fields8Scheme` form could never actually be performed for. -/
theorem deployed_fieldsOpen8_binds_leaf_or_collides
    (path : List (CapMerkleGeneric.StepG Digest8)) {e₁ e₂ : ℤ × ℤ × ℤ}
    (h : Fields8Scheme.recomposeUp8 deployedFields8Scheme
           (Fields8Scheme.fieldsLeafDigest8 deployedFields8Scheme e₁) path
       = Fields8Scheme.recomposeUp8 deployedFields8Scheme
           (Fields8Scheme.fieldsLeafDigest8 deployedFields8Scheme e₂) path) :
    e₁ = e₂ ∨ Fields8Scheme.FieldsOpenColl deployedFields8Scheme e₁ e₂ path :=
  Fields8Scheme.fieldsOpen8_binds_leaf_or_collides deployedFields8Scheme path h

/-! #### §F.D-guards — the inhabitant RUNS (computable witnesses, no `native_decide`). -/

/-- A concrete LINKED IMT fields leaf `(field_key_hash key, fold_bytes32 v, nextAddr)`. -/
def demoFieldsLeaf8A : ℤ × ℤ × ℤ := (7, 1234, 19)

/-- The SAME key and pointer with a different VALUE — the field-write mutation. -/
def demoFieldsLeaf8B : ℤ × ℤ × ℤ := (7, 5678, 19)

/-- The SAME `(key, value)` with a RELINKED pointer — the IMT mutation the 1-felt commitment was blind
to and the 3-field leaf digest is supposed to bind. -/
def demoFieldsLeaf8C : ℤ × ℤ × ℤ := (7, 1234, 23)

/-- A concrete two-level sibling/direction path. -/
def demoFieldsPath8 : List (CapMerkleGeneric.StepG Digest8) :=
  [⟨fun _ => 303, false⟩, ⟨fun _ => 404, true⟩]

-- The deployed inhabitant's fields-leaf digest is a genuine 8-lane vector.
#guard (List.ofFn (Fields8Scheme.fieldsLeafDigest8 deployedFields8Scheme demoFieldsLeaf8A)).length == 8

-- Every lane lands inside the BabyBear range.
#guard (List.ofFn (Fields8Scheme.fieldsLeafDigest8 deployedFields8Scheme demoFieldsLeaf8A)).all
    (fun x => 0 ≤ x && x < BABYBEAR_P)

-- NON-VACUITY, at the inhabitant: writing the field VALUE moves the 8-felt leaf digest.
#guard (List.ofFn (Fields8Scheme.fieldsLeafDigest8 deployedFields8Scheme demoFieldsLeaf8A))
    != (List.ofFn (Fields8Scheme.fieldsLeafDigest8 deployedFields8Scheme demoFieldsLeaf8B))

-- ... and RELINKING the sorted-chain POINTER alone moves it too: the IMT link is genuinely IN the
-- digest, so the chain cannot be rewired under a fixed `(key, value)`.
#guard (List.ofFn (Fields8Scheme.fieldsLeafDigest8 deployedFields8Scheme demoFieldsLeaf8A))
    != (List.ofFn (Fields8Scheme.fieldsLeafDigest8 deployedFields8Scheme demoFieldsLeaf8C))

-- ... and the field write MOVES the recomposed 8-felt fields ROOT along a real two-level path: the
-- whole `node8` membership machinery COMPUTES on the constructed value.
#guard (List.ofFn (Fields8Scheme.recomposeUp8 deployedFields8Scheme
        (Fields8Scheme.fieldsLeafDigest8 deployedFields8Scheme demoFieldsLeaf8A) demoFieldsPath8))
    != (List.ofFn (Fields8Scheme.recomposeUp8 deployedFields8Scheme
        (Fields8Scheme.fieldsLeafDigest8 deployedFields8Scheme demoFieldsLeaf8B) demoFieldsPath8))

/-! ### §F.R — the REFUTABILITY reference chips (both branches are REACHABLE across schemes).

`Compress8CR` is no longer a field, so an injective toy chip is no longer offered as a "non-vacuity"
argument (that was the FALSE COMFORT: toy witness satisfiable, real compressing Poseidon2 false). What
these are FOR now is making §F.S's canaries CONCRETE — at `refFieldsScheme8` the collision disjunct is
genuinely unavailable, and at `badFieldsScheme8` it is genuinely INHABITED. -/

namespace Reference8

open Dregg2.Circuit.DeployedCapTree.Reference8 (refChipAbsorb8 refChip8CR badChipAbsorb8)

/-- The reference 8-felt fields scheme, on the cap tree's injective toy chip (no CR field to supply). -/
def refFieldsScheme8 : Fields8Scheme := ⟨refChipAbsorb8⟩

/-- **THE CANARY, CONCRETE: at this chip NO extracted pair is a collision.** So
`fieldsOpen8_binds_leaf_or_collides` cannot discharge itself on the right — the binding half does the
work, and the disjunction carries strictly more than `True`. -/
theorem refFieldsScheme8_fieldsOpenColl_refutable (e₁ e₂ : ℤ × ℤ × ℤ)
    (path : List (CapMerkleGeneric.StepG Digest8)) :
    ¬ Fields8Scheme.FieldsOpenColl refFieldsScheme8 e₁ e₂ path :=
  Fields8Scheme.fieldsOpenColl_refutable_of_injective refFieldsScheme8 refChip8CR e₁ e₂ path

/-- **AND THE OLD CONCLUSION IS RECOVERED THERE.** At the injective reference chip the deleted GENTIAN
close falls straight out of the new disjunction. -/
theorem refFieldsScheme8_gentian_close (root : Digest8) {e₁ e₂ : ℤ × ℤ × ℤ}
    (path : List (CapMerkleGeneric.StepG Digest8))
    (h₁ : Fields8Scheme.recomposeUp8 refFieldsScheme8
            (Fields8Scheme.fieldsLeafDigest8 refFieldsScheme8 e₁) path = root)
    (h₂ : Fields8Scheme.recomposeUp8 refFieldsScheme8
            (Fields8Scheme.fieldsLeafDigest8 refFieldsScheme8 e₂) path = root) : e₁ = e₂ :=
  Fields8Scheme.membersAt8_functional_on_path_of_injective refFieldsScheme8 refChip8CR root path h₁ h₂

/-- The colliding chip is a `Fields8Scheme` too — and at it the `Coll8` disjunct is genuinely INHABITED,
so the two branches of every `…_or_collides` theorem are BOTH reachable across schemes. -/
def badFieldsScheme8 : Fields8Scheme := ⟨badChipAbsorb8⟩

theorem badFieldsScheme8_has_coll8 : Coll8 badFieldsScheme8.chipAbsorb8 ([0], [1]) :=
  ⟨by simp, rfl⟩

end Reference8

/-! ### §F.ROM — ⚑ THE ROM SUCCESSORS: the fields-tree binding surface as REDUCTIONS on the
PROVED keyed floor.

⚑ STATUS OF THE `…_binds_or_collides` FAMILY (2026-07-24). The §F.X disjunctions are EXTRACTOR
MACHINERY (each hands back the specific colliding pair its reduction consumes), but as EXPORTED
security statements they are shirks: at deployed BabyBear parameters a collision EXISTS by
pigeonhole, so each disjunction is satisfiable through its right branch with NO binding. The
security statements are THIS section's `…_binds_rom` reductions on
`Crypto.RomHashedLeafOpening`'s kit — forger an ORACLE PROGRAM fixed before the oracle is sampled,
closed from `keyedRom_hard` (the birthday bound, a THEOREM), queries PAID, no refuted floor. The
disjunctions are RETAINED for their downstream `rcases` consumers (`VacuitySweepTeeth`,
`Emit.EffectVmEmitRotationV3`, `RotatedKernelRefinementCapFamily`, `InjectiveFloorRegrounded`),
whose re-point is the remaining mechanical work. The modelling step is the cap tree's §7R note
verbatim: one 8-felt child digest = ONE ideal `Fin (2 ^ l)` value; the fixed public chip's own
collision resistance stays a conjecture. -/

section RomSuccessor

open Dregg2.Crypto.RomHashedLeafOpening
open Dregg2.Crypto.RomBindingReduction (RomCarrier romCarrierGame RomCarrierEff)
open Dregg2.Crypto.RomCarrierSites (RomForgeryEff)
open Dregg2.Crypto.FloorGames (Adversary gameAdv)
open Dregg2.Crypto.ConcreteSecurity (Negl PolyBounded)
open Dregg2.Circuit.DeployedCapTree (feltTrunc feltTrunc_inj)

/-- The truncated LINKED IMT fields-leaf block `(addr, value, nextAddr)` at the deployed BabyBear
range — the `[addr, value, nextAddr]` absorb of `heap_root.rs::HeapLeaf::digest8` over a
`fields_root_leaves` entry. -/
abbrev FieldsLeafRomBlock : Type :=
  Fin Dregg2.Crypto.RomCarrierSites.babyBearP × Fin Dregg2.Crypto.RomCarrierSites.babyBearP
    × Fin Dregg2.Crypto.RomCarrierSites.babyBearP

/-- **THE FIELDS-TREE ROM FAMILY** at tag space `Key`: truncated 3-limb IMT leaf blocks ⊕ ordered
ideal-digest node pairs (the deployed 3-vs-16 arity separation, by constructor). -/
abbrev fieldsRomFamily (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key)
    (kN : Nonempty Key) : Dregg2.Crypto.KeyedRomFloor.KeyedRomFamily :=
  hlFam Key kF kD kN (fun _ => FieldsLeafRomBlock) (fun _ => inferInstance)
    (fun _ => inferInstance)

/-- The fields-leaf carrier — the leaf digest binds the WHOLE linked triple: the hashed field KEY,
the folded VALUE, and the sorted-chain IMT POINTER. -/
abbrev fieldsLeafRomCarrier (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key)
    (kN : Nonempty Key) : RomCarrier (fieldsRomFamily Key kF kD kN) :=
  hlLeafCarrier Key kF kD kN (fun _ => FieldsLeafRomBlock) (fun _ => inferInstance)
    (fun _ => inferInstance)

/-- The fields-node carrier — the `node8` digest binds BOTH ordered children. -/
abbrev fieldsNodeRomCarrier (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key)
    (kN : Nonempty Key) : RomCarrier (fieldsRomFamily Key kF kD kN) :=
  hlNodeCarrier Key kF kD kN (fun _ => FieldsLeafRomBlock) (fun _ => inferInstance)
    (fun _ => inferInstance)

/-- **⚑⚑ THE FIELDS-LEAF BINDING, AS A REDUCTION** — ROM successor of
`fieldsLeafDigest8_binds_or_collides`'s left disjunct: a query-bounded forger that equivocates one
leaf digest between two DISTINCT linked triples has NEGLIGIBLE advantage. In particular the IMT
POINTER is bound: relinking the sorted chain under a fixed `(key, value)` is an equivocation. -/
theorem fieldsLeafDigest8_binds_rom (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key)
    (kN : Nonempty Key) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (romCarrierGame (fieldsRomFamily Key kF kD kN)
      (fieldsLeafRomCarrier Key kF kD kN)))
    (hA : RomCarrierEff (fieldsRomFamily Key kF kD kN)
      (fieldsLeafRomCarrier Key kF kD kN) Q A) :
    Negl (gameAdv (romCarrierGame (fieldsRomFamily Key kF kD kN)
      (fieldsLeafRomCarrier Key kF kD kN)) A) :=
  hlLeaf_binds_rom Key kF kD kN _ _ _ Q hQ A hA

/-- **⚑⚑ THE FIELDS-NODE BINDING, AS A REDUCTION** — ROM successor of
`fieldsNodeOf8_binds_or_collides`'s left disjunct. -/
theorem fieldsNodeOf8_binds_rom (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key)
    (kN : Nonempty Key) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (romCarrierGame (fieldsRomFamily Key kF kD kN)
      (fieldsNodeRomCarrier Key kF kD kN)))
    (hA : RomCarrierEff (fieldsRomFamily Key kF kD kN)
      (fieldsNodeRomCarrier Key kF kD kN) Q A) :
    Negl (gameAdv (romCarrierGame (fieldsRomFamily Key kF kD kN)
      (fieldsNodeRomCarrier Key kF kD kN)) A) :=
  hlNode_binds_rom Key kF kD kN _ _ _ Q hQ A hA

/-- **⚑⚑ THE FIELDS SPINE BINDING, AS A REDUCTION** — ROM successor of
`recomposeUp8_binds_or_collides`: two DISTINCT starting digests folding one SHARED schedule to one
root cost an interior node collision, found by the paying walk. -/
theorem fieldsRecomposeUp8_binds_rom (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key)
    (kN : Nonempty Key) (dep Q Q' : ℕ → ℕ)
    (hle : ∀ l, Q l + 2 * dep l ≤ Q' l)
    (hQ' : PolyBounded (fun l => ((Q' l : ℝ) * (Q' l : ℝ) + 1)))
    (A : Adversary (hlPathForgery Key kF kD kN (fun _ => FieldsLeafRomBlock)
      (fun _ => inferInstance) (fun _ => inferInstance) dep).game)
    (hA : RomForgeryEff (fieldsRomFamily Key kF kD kN)
      (hlPathForgery Key kF kD kN (fun _ => FieldsLeafRomBlock)
        (fun _ => inferInstance) (fun _ => inferInstance) dep) Q A) :
    Negl (gameAdv (hlPathForgery Key kF kD kN (fun _ => FieldsLeafRomBlock)
      (fun _ => inferInstance) (fun _ => inferInstance) dep).game A) :=
  hlPathRom_binds Key kF kD kN _ _ _ dep Q Q' hle hQ' A hA

/-- **⚑⚑ THE GENTIAN CLOSE, AS A REDUCTION** — ROM successor of
`fieldsOpen8_binds_leaf_or_collides` (and of its deployed instantiation
`deployed_fieldsOpen8_binds_leaf_or_collides` — the ROM statement is about the SAMPLED oracle, so
the ∀-scheme and at-the-inhabitant forms collapse into one): a query-bounded forger that opens one
8-felt fields root to two DISTINCT linked leaves along one shared path has NEGLIGIBLE advantage.
The lane-0 forge the GENTIAN weld exhibits is priced here as a genuine attack on the model, not
excluded by a refuted premise. -/
theorem fieldsOpen8_binds_leaf_rom (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key)
    (kN : Nonempty Key) (dep Q Q' : ℕ → ℕ)
    (hle : ∀ l, Q l + (2 * dep l + 2) ≤ Q' l)
    (hQ' : PolyBounded (fun l => ((Q' l : ℝ) * (Q' l : ℝ) + 1)))
    (A : Adversary (hlOpenForgery Key kF kD kN (fun _ => FieldsLeafRomBlock)
      (fun _ => inferInstance) (fun _ => inferInstance) dep).game)
    (hA : RomForgeryEff (fieldsRomFamily Key kF kD kN)
      (hlOpenForgery Key kF kD kN (fun _ => FieldsLeafRomBlock)
        (fun _ => inferInstance) (fun _ => inferInstance) dep) Q A) :
    Negl (gameAdv (hlOpenForgery Key kF kD kN (fun _ => FieldsLeafRomBlock)
      (fun _ => inferInstance) (fun _ => inferInstance) dep).game A) :=
  hlOpenRom_binds Key kF kD kN _ _ _ dep Q Q' hle hQ' A hA

/-- **⚑ THE PUBLISHED-ROOT FORM** — ROM successor of
`membersAt8_functional_on_path_or_collides`: two query-bounded openings of ONE published root to
two DISTINCT linked leaves succeed with negligible probability. -/
theorem fieldsMembersAt8_functional_rom (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key)
    (kN : Nonempty Key) (dep Q Q' : ℕ → ℕ)
    (hle : ∀ l, Q l + (2 * dep l + 2) ≤ Q' l)
    (hQ' : PolyBounded (fun l => ((Q' l : ℝ) * (Q' l : ℝ) + 1)))
    (A : Adversary (hlOpenRootForgery Key kF kD kN (fun _ => FieldsLeafRomBlock)
      (fun _ => inferInstance) (fun _ => inferInstance) dep).game)
    (hA : RomForgeryEff (fieldsRomFamily Key kF kD kN)
      (hlOpenRootForgery Key kF kD kN (fun _ => FieldsLeafRomBlock)
        (fun _ => inferInstance) (fun _ => inferInstance) dep) Q A) :
    Negl (gameAdv (hlOpenRootForgery Key kF kD kN (fun _ => FieldsLeafRomBlock)
      (fun _ => inferInstance) (fun _ => inferInstance) dep).game A) :=
  hlOpenRootRom_binds Key kF kD kN _ _ _ dep Q Q' hle hQ' A hA

/-- The truncation pin: a range-bounded deployed IMT triple embeds LOSSLESSLY, so a distinct pair
of deployed leaves stays a distinct pair of ROM payloads. -/
def fieldsLeafRomBlockOf (e : ℤ × ℤ × ℤ) : FieldsLeafRomBlock :=
  (feltTrunc e.1, feltTrunc e.2.1, feltTrunc e.2.2)

theorem fieldsLeafRomBlockOf_inj {e₁ e₂ : ℤ × ℤ × ℤ}
    (h₁ : ∀ x ∈ [e₁.1, e₁.2.1, e₁.2.2], 0 ≤ x ∧ x < BABYBEAR_P)
    (h₂ : ∀ x ∈ [e₂.1, e₂.2.1, e₂.2.2], 0 ≤ x ∧ x < BABYBEAR_P)
    (h : fieldsLeafRomBlockOf e₁ = fieldsLeafRomBlockOf e₂) : e₁ = e₂ := by
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
theorem deployedShape_fieldsOpen8_binds_leaf_rom (dep Q Q' : ℕ → ℕ)
    (hle : ∀ l, Q l + (2 * dep l + 2) ≤ Q' l)
    (hQ' : PolyBounded (fun l => ((Q' l : ℝ) * (Q' l : ℝ) + 1)))
    (A : Adversary (hlOpenForgery Unit inferInstance inferInstance inferInstance
      (fun _ => FieldsLeafRomBlock) (fun _ => inferInstance) (fun _ => inferInstance) dep).game)
    (hA : RomForgeryEff (fieldsRomFamily Unit inferInstance inferInstance inferInstance)
      (hlOpenForgery Unit inferInstance inferInstance inferInstance
        (fun _ => FieldsLeafRomBlock) (fun _ => inferInstance) (fun _ => inferInstance) dep)
      Q A) :
    Negl (gameAdv (hlOpenForgery Unit inferInstance inferInstance inferInstance
      (fun _ => FieldsLeafRomBlock) (fun _ => inferInstance) (fun _ => inferInstance) dep).game
      A) :=
  fieldsOpen8_binds_leaf_rom Unit inferInstance inferInstance inferInstance dep Q Q' hle hQ' A hA

end RomSuccessor

/-! ### §F.A — Axiom hygiene. -/
-- §F.ROM — the ROM successors (reductions on the proved keyed floor; no bare disjunction).
#assert_axioms fieldsLeafDigest8_binds_rom
#assert_axioms fieldsNodeOf8_binds_rom
#assert_axioms fieldsRecomposeUp8_binds_rom
#assert_axioms fieldsOpen8_binds_leaf_rom
#assert_axioms fieldsMembersAt8_functional_rom
#assert_axioms fieldsLeafRomBlockOf_inj
#assert_axioms deployedShape_fieldsOpen8_binds_leaf_rom

#assert_axioms Fields8Scheme.fieldsLeafBlock_inj
#assert_axioms Fields8Scheme.fieldsLeafDigest8_binds_or_collides
#assert_axioms Fields8Scheme.fieldsNodeOf8_binds_or_collides
#assert_axioms Fields8Scheme.recomposeUp8_binds_or_collides
#assert_axioms Fields8Scheme.fieldsOpen8_binds_leaf_or_collides
#assert_axioms Fields8Scheme.membersAt8_functional_on_path_or_collides
#assert_axioms Fields8Scheme.fieldsOpenColl_refutable_of_injective
#assert_axioms Fields8Scheme.fieldsLeafDigest8_injective_of_injective
#assert_axioms Fields8Scheme.fieldsNodeOf8_injective_of_injective
#assert_axioms Fields8Scheme.recomposeUp8_inj_of_path_of_injective
#assert_axioms Fields8Scheme.membersAt8_functional_on_path_of_injective
#assert_axioms deployedFields8Scheme_chip
#assert_axioms deployed_fieldsOpen8_binds_leaf_or_collides
#assert_axioms Reference8.refFieldsScheme8_fieldsOpenColl_refutable
#assert_axioms Reference8.refFieldsScheme8_gentian_close
#assert_axioms Reference8.badFieldsScheme8_has_coll8

end Dregg2.Circuit.DeployedFieldsTree

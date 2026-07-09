/-
# Dregg2.Deos.DocMergeComposed — the COMPOSED-DOCUMENT merge is a PRODUCT OF PUSHOUTS.

`docs/DREGG-DOCUMENT-FOUNDATION.md` §1.2, §1.5, §2-F1, §3. Differential target: the Rust crate
`dregg-doc/src/composition.rs::{Composed, merge_composed}` (`merge_composed`, composition.rs:1036).

**What this file is (Foundation piece F1, composed half).** `DocMerge.lean` proves the single-cell
merge algebra over a keyed atom map (`AtomId → Option AtomVal`) is the least-upper-bound JOIN and the
pushout in the THIN inclusion category. A dreggverse document is not one cell but a FAMILY of cells:
a parent LAYOUT graph plus, by reference, a map `CellId → DocGraph` of independently-owned child
graphs (§1.5 "structure is cells; content is atoms"). This file lifts the single-cell result to that
family.

**The family INDEX carries cross-cell identity — we do NOT flatten (§2-F1, deliberately).** The design
briefing is explicit: cross-cell identity is the family index `CellId`; within a cell `AtomId` stays
local. The global `(CellId, AtomId)` pair is a DOWNSTREAM refinement for atom-range transclusion,
OUT OF SCOPE here. So `ComposedDoc` is `layout : DocGraph` + `children : CellId → Option DocGraph`,
and `mergeComposed` is the COMPONENTWISE merge: the layout via `DocMerge.merge`, each child via
`DocMerge.merge`. The `AtomId` spaces of distinct components never meet — that disjointness IS the
theorem (§1.2).

**The load-bearing new theorem — the BOUNDARY LEMMA (`boundary_layout_child_disjoint`).** Because the
components are disjoint, a change confined to `children c` and a change confined to `layout` (or to a
different child `c'`) never interact: the merge's layout coordinate is a function of ONLY the two
layouts, and the merge's child-`c` coordinate is a function of ONLY the two child-`c` graphs. "A
child-content edit can NEVER conflict with a layout edit" (§1.2, the confinement boundary; the Rust
test `layout_edit_and_child_edit_do_not_conflict`, composition.rs:1342) is made a theorem — it rests
GENUINELY on component-disjointness (a flattened shared `AtomId` space would destroy it).

**Honest scoping (inherited from `DocMerge.lean`:11–52, unchanged).** This is the THIN/preorder
category over `AtomVal := Status` (liveness bits). The full labelled patch category `P` is a named
residual we do NOT build. Composition changes the CARRIER (a family), not the merge — the single-cell
lattice is reused wholesale, never re-derived.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}).
Verified with `lake build Dregg2.Deos.DocMergeComposed`.
-/
import Dregg2.Deos.DocMerge
import Dregg2.Tactics

namespace Dregg2.Deos.DocMergeComposed

open Dregg2.Deos.DocMerge

/-! ## 1. The composed carrier — a FAMILY of `DocGraph`s indexed by `CellId`.

`composition.rs::Composed` = `{ layout : LayoutGraph, children : BTreeMap<CellId, LayoutGraph> }`.
We keep the parent layout as one `DocGraph` and the children as a keyed map `CellId → Option DocGraph`
(the `BTreeMap` — `none` = a `CellId` not embedded). `CellId` is opaque (`composition.rs::CellId(u128)`),
distinct from `AtomId`: it is the FAMILY INDEX, not an atom. -/

/-- A child-cell id (`composition.rs::CellId`); opaque, the FAMILY INDEX. Distinct from `AtomId`:
the cross-cell identity lives HERE, not in a flattened `(CellId, AtomId)` atom key (that is the
downstream transclusion refinement, out of scope — §2-F1). -/
abbrev CellId := Nat

/-- **`ComposedDoc`** — a composed document (`composition.rs::Composed`): a parent LAYOUT graph plus,
by reference, each embedded child's own graph. Two levels (§1.5): ACROSS cells = this family;
WITHIN a cell = a `DocGraph` (the already-proven patch core). -/
structure ComposedDoc where
  /-- The parent's layout graph (`composition.rs::Composed::layout`). -/
  layout : DocGraph
  /-- Each embedded child's own graph (`composition.rs::Composed::children`); `none` = not embedded. -/
  children : CellId → Option DocGraph

/-- Componentwise extensionality for `ComposedDoc` (function field `children` reduces to `funext`). -/
theorem ComposedDoc.ext {a b : ComposedDoc}
    (hl : a.layout = b.layout) (hc : ∀ c, a.children c = b.children c) : a = b := by
  cases a; cases b
  simp only [ComposedDoc.mk.injEq]
  exact ⟨hl, funext hc⟩

/-! ## 2. The `Option`-lifted single-cell join — `childJoin` = per-cell `DocMerge.merge`.

`merge_composed` (composition.rs:1036) merges each child INDEPENDENTLY: a cell present in both sides
merges by the child's OWN `union_in_place` (= `DocMerge.merge`); a cell present on one side only
carries through. This is `atomJoin`'s shape (DocMerge:146) lifted to `Option DocGraph` with
`DocMerge.merge` as the fibre join — exactly a product of the single-cell algebra over the index. -/

/-- The `Option`-lifted per-cell join: a `CellId` present in both merges its two `DocGraph`s by
`DocMerge.merge`; present on one side only, that side's graph carries (`composition.rs:1036`'s
`.and_modify(union_in_place).or_insert`). -/
def childJoin : Option DocGraph → Option DocGraph → Option DocGraph
  | some a, some b => some (DocMerge.merge a b)
  | some a, none   => some a
  | none,   some b => some b
  | none,   none   => none

@[simp] theorem childJoin_some_some (a b : DocGraph) :
    childJoin (some a) (some b) = some (DocMerge.merge a b) := rfl
@[simp] theorem childJoin_some_none (a : DocGraph) : childJoin (some a) none = some a := rfl
@[simp] theorem childJoin_none_left (x : Option DocGraph) : childJoin none x = x := by
  cases x <;> rfl

/-- `childJoin` is COMMUTATIVE — reusing single-cell `merge_comm` in the both-present fibre. -/
theorem childJoin_comm (x y : Option DocGraph) : childJoin x y = childJoin y x := by
  cases x <;> cases y <;> simp only [childJoin, DocMerge.merge_comm]

/-- `childJoin` is ASSOCIATIVE — reusing single-cell `merge_assoc`. -/
theorem childJoin_assoc (x y z : Option DocGraph) :
    childJoin (childJoin x y) z = childJoin x (childJoin y z) := by
  cases x <;> cases y <;> cases z <;> simp only [childJoin, DocMerge.merge_assoc]

/-- `childJoin` is IDEMPOTENT — reusing single-cell `merge_idem`. -/
@[simp] theorem childJoin_idem (x : Option DocGraph) : childJoin x x = x := by
  cases x <;> simp only [childJoin, DocMerge.merge_idem]

/-! ## 3. `mergeComposed` — the COMPONENTWISE merge (the product of pushouts, `merge_composed`). -/

/-- **`mergeComposed a b`** (`composition.rs::merge_composed`, composition.rs:1036) — the PRODUCT OF
PUSHOUTS: the layout pushout (`DocMerge.merge` on layouts) PLUS each child's own pushout
(`childJoin`), independently. Total by construction; the layout and every child are merged in
SEPARATE `AtomId` spaces, so no cross-component interaction is even expressible. -/
def mergeComposed (a b : ComposedDoc) : ComposedDoc where
  layout := DocMerge.merge a.layout b.layout
  children := fun c => childJoin (a.children c) (b.children c)

@[simp] theorem mergeComposed_layout (a b : ComposedDoc) :
    (mergeComposed a b).layout = DocMerge.merge a.layout b.layout := rfl
@[simp] theorem mergeComposed_children (a b : ComposedDoc) (c : CellId) :
    (mergeComposed a b).children c = childJoin (a.children c) (b.children c) := rfl

/-- **`mergeComposed_comm`.** Componentwise: layout by `merge_comm`, each child by `childJoin_comm`. -/
theorem mergeComposed_comm (a b : ComposedDoc) : mergeComposed a b = mergeComposed b a := by
  apply ComposedDoc.ext
  · exact DocMerge.merge_comm a.layout b.layout
  · intro c; exact childJoin_comm (a.children c) (b.children c)

/-- **`mergeComposed_assoc`.** Componentwise: layout by `merge_assoc`, each child by `childJoin_assoc`. -/
theorem mergeComposed_assoc (a b c : ComposedDoc) :
    mergeComposed (mergeComposed a b) c = mergeComposed a (mergeComposed b c) := by
  apply ComposedDoc.ext
  · exact DocMerge.merge_assoc a.layout b.layout c.layout
  · intro cell; exact childJoin_assoc (a.children cell) (b.children cell) (c.children cell)

/-- **`mergeComposed_idem`.** Componentwise: layout by `merge_idem`, each child by `childJoin_idem`. -/
theorem mergeComposed_idem (a : ComposedDoc) : mergeComposed a a = a := by
  apply ComposedDoc.ext
  · exact DocMerge.merge_idem a.layout
  · intro c; exact childJoin_idem (a.children c)

/-- **`mergeComposed_total`.** `mergeComposed` is a TOTAL function — every pair of composed forks has
a merge (no `Option`/error result; the union of the family always exists). -/
theorem mergeComposed_total (a b : ComposedDoc) : ∃ d : ComposedDoc, d = mergeComposed a b :=
  ⟨mergeComposed a b, rfl⟩

/-! ## 4. The componentwise inclusion order `⊑c` and the UNIVERSAL PROPERTY (LUB), lifted.

`⊑c` is the single-cell `⊑` on the layout AND, on each `CellId`, the `Option`-lifted `⊑`. The whole
lattice is the single-cell one reused per component — `mergeComposed` is its LUB, proved by lifting
`merge_is_lub` (`merge_includes_left/right`, `merge_least`) coordinate by coordinate. -/

/-- **`IncludesOpt x y`** — the `Option`-lifted single-cell inclusion `⊑`: an ABSENT cell (`none`) is
below everything (bottom); a present cell is below only a present cell it `⊑`-includes into; a present
cell is never below `none` (a cell, once embedded, cannot vanish). -/
def IncludesOpt : Option DocGraph → Option DocGraph → Prop
  | none,   _      => True
  | some _, none   => False
  | some g, some h => g ⊑ h

@[simp] theorem IncludesOpt_none_left (x : Option DocGraph) : IncludesOpt none x := trivial
@[simp] theorem IncludesOpt_some_some (g h : DocGraph) :
    IncludesOpt (some g) (some h) = (g ⊑ h) := rfl

theorem IncludesOpt.refl (x : Option DocGraph) : IncludesOpt x x := by
  cases x with
  | none => trivial
  | some g => exact Includes.refl g

theorem IncludesOpt.trans {x y z : Option DocGraph}
    (hxy : IncludesOpt x y) (hyz : IncludesOpt y z) : IncludesOpt x z := by
  cases x with
  | none => trivial
  | some g =>
    cases y with
    | none => exact absurd hxy (by simp [IncludesOpt])
    | some h =>
      cases z with
      | none => exact absurd hyz (by simp [IncludesOpt])
      | some k => exact Includes.trans hxy hyz

theorem IncludesOpt.antisymm {x y : Option DocGraph}
    (hxy : IncludesOpt x y) (hyx : IncludesOpt y x) : x = y := by
  cases x with
  | none => cases y with
    | none => rfl
    | some h => exact absurd hyx (by simp [IncludesOpt])
  | some g => cases y with
    | none => exact absurd hxy (by simp [IncludesOpt])
    | some h => rw [Includes.antisymm hxy hyx]

/-- `childJoin` is an upper bound for its LEFT input in `IncludesOpt` — the left cocone leg per cell,
lifting `merge_includes_left`. -/
theorem childJoin_includesOpt_left (x y : Option DocGraph) : IncludesOpt x (childJoin x y) := by
  cases x with
  | none => trivial
  | some a => cases y with
    | none => exact Includes.refl a
    | some b => exact merge_includes_left a b

/-- `childJoin` is an upper bound for its RIGHT input — the right cocone leg per cell. -/
theorem childJoin_includesOpt_right (x y : Option DocGraph) : IncludesOpt y (childJoin x y) := by
  cases x with
  | none => cases y with
    | none => trivial
    | some b => exact Includes.refl b
  | some a => cases y with
    | none => trivial
    | some b => exact merge_includes_right a b

/-- `childJoin` is the LEAST upper bound per cell: any common `IncludesOpt`-bound dominates it,
lifting `merge_least`. -/
theorem childJoin_includesOpt_least {x y u : Option DocGraph}
    (hx : IncludesOpt x u) (hy : IncludesOpt y u) : IncludesOpt (childJoin x y) u := by
  cases x with
  | none => cases y with
    | none => trivial
    | some b => simpa [childJoin] using hy
  | some a => cases y with
    | none => simpa [childJoin] using hx
    | some b =>
      cases u with
      | none => exact absurd hx (by simp [IncludesOpt])
      | some w => exact merge_least (a := a) (b := b) (u := w) hx hy

/-- **`IncludesC a b` (`a ⊑c b`).** Composed inclusion: `b` advances past `a` in EVERY component —
the layout by `⊑`, and each `CellId` by `IncludesOpt`. The componentwise (product) order. -/
def IncludesC (a b : ComposedDoc) : Prop :=
  a.layout ⊑ b.layout ∧ ∀ c, IncludesOpt (a.children c) (b.children c)

@[inherit_doc] infix:50 " ⊑c " => IncludesC

theorem IncludesC.refl (a : ComposedDoc) : a ⊑c a :=
  ⟨Includes.refl a.layout, fun c => IncludesOpt.refl (a.children c)⟩

theorem IncludesC.trans {a b c : ComposedDoc} (hab : a ⊑c b) (hbc : b ⊑c c) : a ⊑c c :=
  ⟨Includes.trans hab.1 hbc.1, fun cell => IncludesOpt.trans (hab.2 cell) (hbc.2 cell)⟩

/-- **`IncludesC.antisymm`.** `⊑c` is ANTISYMMETRIC — with `refl`/`trans`, a PARTIAL ORDER (so the
thin composed category has only identity isos). Componentwise `Includes.antisymm` /
`IncludesOpt.antisymm` + `funext`. -/
theorem IncludesC.antisymm {a b : ComposedDoc} (hab : a ⊑c b) (hba : b ⊑c a) : a = b := by
  apply ComposedDoc.ext
  · exact Includes.antisymm hab.1 hba.1
  · intro c; exact IncludesOpt.antisymm (hab.2 c) (hba.2 c)

/-- **`mergeComposed_includesC_left` (a cocone leg).** `a ⊑c mergeComposed a b`: layout by
`merge_includes_left`, each child by `childJoin_includesOpt_left`. -/
theorem mergeComposed_includesC_left (a b : ComposedDoc) : a ⊑c mergeComposed a b :=
  ⟨merge_includes_left a.layout b.layout,
   fun c => childJoin_includesOpt_left (a.children c) (b.children c)⟩

/-- **`mergeComposed_includesC_right` (the other cocone leg).** `b ⊑c mergeComposed a b`. -/
theorem mergeComposed_includesC_right (a b : ComposedDoc) : b ⊑c mergeComposed a b :=
  ⟨merge_includes_right a.layout b.layout,
   fun c => childJoin_includesOpt_right (a.children c) (b.children c)⟩

/-- **`mergeComposed_least` (LEASTNESS).** Any common `⊑c`-upper-bound `u` dominates the merge:
layout by `merge_least`, each child by `childJoin_includesOpt_least`. -/
theorem mergeComposed_least {a b u : ComposedDoc} (ha : a ⊑c u) (hb : b ⊑c u) :
    mergeComposed a b ⊑c u :=
  ⟨merge_least ha.1 hb.1,
   fun c => childJoin_includesOpt_least (ha.2 c) (hb.2 c)⟩

/-- **`mergeComposed_is_lub` (THE UNIVERSAL PROPERTY, lifted componentwise).** `mergeComposed a b`
is the LEAST UPPER BOUND of `a` and `b` in `⊑c`: it includes both legs AND lies below every common
upper bound. Lifted from the single-cell `merge_is_lub` component by component (layout + each child),
NOT re-derived. -/
theorem mergeComposed_is_lub (a b : ComposedDoc) :
    a ⊑c mergeComposed a b ∧ b ⊑c mergeComposed a b ∧
    (∀ u, a ⊑c u → b ⊑c u → mergeComposed a b ⊑c u) :=
  ⟨mergeComposed_includesC_left a b, mergeComposed_includesC_right a b,
   fun _ ha hb => mergeComposed_least ha hb⟩

/-! ## 5. THE PRODUCT OF PUSHOUTS — `mergeComposed` is the pushout in the composed thin category,
and EACH coordinate is a single-cell pushout (literally `DocMerge.merge_isPushout`). -/

/-- **`IsCoconeC a b d`** — `d` is a cocone over `a`, `b` (both include, `a ⊑c d ∧ b ⊑c d`). -/
def IsCoconeC (a b d : ComposedDoc) : Prop := a ⊑c d ∧ b ⊑c d

/-- **`IsPushoutC o a b d`** — `d` is the pushout of the span `a ⊑c← o →⊑c b` in the composed thin
category: `o` includes into both feet, `d` is the LEAST cocone over the feet. In a poset the apex `o`
contributes no extra constraint — the pushout is the join of the feet (componentwise). -/
def IsPushoutC (o a b d : ComposedDoc) : Prop :=
  o ⊑c a ∧ o ⊑c b ∧ IsCoconeC a b d ∧ ∀ d', IsCoconeC a b d' → d ⊑c d'

/-- **`mergeComposed_isPushout` (mergeComposed IS the composed pushout).** For any span
`a ⊑c← o →⊑c b`, the join `mergeComposed a b` is its pushout in the composed thin category. Cocone
legs = `mergeComposed_includesC_left/right`; universality = `mergeComposed_least`. The apex `o` plays
no role in the colimit object (the poset pushout is the join of the two FEET). -/
theorem mergeComposed_isPushout (o a b : ComposedDoc) (hoa : o ⊑c a) (hob : o ⊑c b) :
    IsPushoutC o a b (mergeComposed a b) := by
  refine ⟨hoa, hob, ⟨mergeComposed_includesC_left a b, mergeComposed_includesC_right a b⟩, ?_⟩
  intro d' hd'
  exact mergeComposed_least hd'.1 hd'.2

/-- **`pushoutC_unique` (UNIQUE UP TO ISO = EQUALITY).** Any two pushouts of the same composed span
are EQUAL, via `IncludesC.antisymm` (the only isos in the poset are identities). -/
theorem pushoutC_unique {o a b d d' : ComposedDoc}
    (hd : IsPushoutC o a b d) (hd' : IsPushoutC o a b d') : d = d' := by
  obtain ⟨_, _, hcone, huniv⟩ := hd
  obtain ⟨_, _, hcone', huniv'⟩ := hd'
  exact IncludesC.antisymm (huniv d' hcone') (huniv' d hcone)

/-- **`mergeComposed_layout_is_pushout` (the LAYOUT coordinate is a single-cell pushout).** The
layout component of `mergeComposed a b` is EXACTLY the single-cell pushout of the layouts — literally
`DocMerge.merge_isPushout`. This is the "product of pushouts" made explicit at the layout factor. -/
theorem mergeComposed_layout_is_pushout (o a b : ComposedDoc) (hoa : o ⊑c a) (hob : o ⊑c b) :
    IsPushout o.layout a.layout b.layout (mergeComposed a b).layout :=
  DocMerge.merge_isPushout o.layout a.layout b.layout hoa.1 hob.1

/-- **`mergeComposed_child_is_pushout` (each CHILD coordinate is a single-cell pushout).** For a
`CellId` embedded in the span apex and both feet (`o`/`a`/`b` all have `some` there), the child
coordinate of `mergeComposed a b` is `some` of the single-cell pushout of the two child graphs —
literally `DocMerge.merge_isPushout` in that child's OWN `AtomId` space. Together with
`mergeComposed_layout_is_pushout` this is the PRODUCT-OF-PUSHOUTS structure component by component. -/
theorem mergeComposed_child_is_pushout {o a b : ComposedDoc} (c : CellId)
    {go ga gb : DocGraph}
    (_ho : o.children c = some go) (ha : a.children c = some ga) (hb : b.children c = some gb)
    (hoa : go ⊑ ga) (hob : go ⊑ gb) :
    (mergeComposed a b).children c = some (DocMerge.merge ga gb) ∧
    IsPushout go ga gb (DocMerge.merge ga gb) := by
  refine ⟨?_, DocMerge.merge_isPushout go ga gb hoa hob⟩
  rw [mergeComposed_children, ha, hb, childJoin_some_some]

/-! ## 6. THE BOUNDARY LEMMA — a child-content edit can NEVER conflict with a layout edit (§1.2).

The load-bearing NEW theorem. Because the components are DISJOINT `AtomId` spaces, an edit confined to
`children c` and an edit confined to the `layout` (or to a different child `c'`) never interact. We
prove exactly that: with a common base `o`, if author A's edit is confined to the layout
(`children` unchanged) and author B's is confined to child `c` (layout unchanged, every OTHER child
unchanged), then the merge SEPARATES CLEANLY — the layout coordinate is a function of ONLY the two
layouts (A's edit + base), the child-`c` coordinate a function of ONLY the two child-`c` graphs
(B's edit + base), and every untouched component is unchanged. This rests GENUINELY on
component-disjointness: `childJoin_idem` collapses the untouched cells, and the layout/child factors
never share an `AtomId`. It is the Rust `layout_edit_and_child_edit_do_not_conflict`
(composition.rs:1342) as a `∀`-theorem. -/

/-- **`boundary_layout_child_disjoint` (THE BOUNDARY LEMMA).** Common base `o`; author A confined to
the layout (`dA.children = o.children`); author B confined to child `c` (`dB.layout = o.layout` and
`dB.children c' = o.children c'` for every `c' ≠ c`). Then the composed merge separates by component:
the layout is A's-layout-merged-with-base (independent of B's child edit), the edited child `c` is
base-merged-with-B's-edit (independent of A's layout edit), and every other component is the base's,
untouched. A layout edit and a child edit CANNOT meet — they live in disjoint `AtomId` spaces. -/
theorem boundary_layout_child_disjoint {o dA dB : ComposedDoc} (c : CellId)
    (hA : dA.children = o.children)
    (hB_layout : dB.layout = o.layout)
    (hB_other : ∀ c', c' ≠ c → dB.children c' = o.children c') :
    (mergeComposed dA dB).layout = DocMerge.merge dA.layout o.layout ∧
    (mergeComposed dA dB).children c = childJoin (o.children c) (dB.children c) ∧
    (∀ c', c' ≠ c → (mergeComposed dA dB).children c' = o.children c') := by
  refine ⟨?_, ?_, ?_⟩
  · -- The layout merge sees ONLY the two layouts; B contributed only the base layout.
    rw [mergeComposed_layout, hB_layout]
  · -- The child-c merge sees ONLY the two child-c graphs; A contributed only the base child c.
    rw [mergeComposed_children, hA]
  · -- Every OTHER component is the base merged with itself = itself (childJoin_idem).
    intro c' hc'
    rw [mergeComposed_children, hA, hB_other c' hc', childJoin_idem]

/-- **`boundary_no_cross_perturbation` (the sharp disjointness core).** Re-stating the boundary as
FRAME independence: the layout coordinate of the merge is invariant under ARBITRARY replacement of
BOTH sides' entire child families, and each child coordinate is invariant under arbitrary replacement
of BOTH sides' layouts and all OTHER children. So a child edit perturbs no layout merge and no other
child merge, and a layout edit perturbs no child merge — the disjoint-product content, with no base
or confinement hypotheses at all. -/
theorem boundary_no_cross_perturbation (a b : ComposedDoc)
    (chA chB : CellId → Option DocGraph) (layA layB : DocGraph) :
    (mergeComposed a b).layout
      = (mergeComposed ⟨a.layout, chA⟩ ⟨b.layout, chB⟩).layout
    ∧ ∀ c, (mergeComposed a b).children c
      = (mergeComposed ⟨layA, a.children⟩ ⟨layB, b.children⟩).children c := by
  refine ⟨rfl, ?_⟩
  intro c; rfl

/-- **`boundary_no_joint_conflict` (NO CROSS-AUTHOR CONFLICT, at the `ConflictAt` level).** The prose
claim of §1.2 ("a child-content edit and a layout edit can never conflict") stated in the actual
conflict predicate `DocMerge.ConflictAt`, not merely as decomposition. With author A confined to the
layout (`dA.children = o.children`) and author B leaving the layout at the base (`dB.layout = o.layout`):
* **(1) layout:** every `ConflictAt` in the merged layout is already a conflict between A's layout and
  the BASE `o.layout` — author B contributed nothing to it (B's layout IS the base);
* **(2) children:** every `ConflictAt` in any merged child coordinate lives in the BASE-vs-B merge of
  that cell (`childJoin (o.children c') (dB.children c')`) — author A contributed nothing (A's children
  ARE the base, in every cell).
So no conflict in the composed merge is JOINTLY caused by the two authors: layout conflicts are
{A, base}-only, child conflicts are {B, base}-only. They never interact — disjoint `AtomId` spaces.
(Note: `hB_other` from the boundary lemma is not even needed — this is stronger.) -/
theorem boundary_no_joint_conflict {o dA dB : ComposedDoc}
    (hA : dA.children = o.children) (hB_layout : dB.layout = o.layout) :
    (∀ p x y, ConflictAt (mergeComposed dA dB).layout p x y →
              ConflictAt (DocMerge.merge dA.layout o.layout) p x y) ∧
    (∀ c' g p x y, (mergeComposed dA dB).children c' = some g → ConflictAt g p x y →
              childJoin (o.children c') (dB.children c') = some g) := by
  refine ⟨?_, ?_⟩
  · intro p x y h
    have e : (mergeComposed dA dB).layout = DocMerge.merge dA.layout o.layout := by
      rw [mergeComposed_layout, hB_layout]
    rwa [e] at h
  · intro c' g p x y hg _
    rw [mergeComposed_children, hA] at hg
    exact hg

/-! ## 7. NON-VACUITY, both poles — a genuine firing, and a concrete two-author boundary scenario.

The load-bearing-spec teeth (§3): a vacuous `P → P` is a FAILURE. Below: (a) a concrete `ComposedDoc`
pair where `mergeComposed` genuinely FIRES (a real child + a real layout, both merged); (b) a concrete
two-author scenario — author A edits child `cellA`, author B edits the layout — where `mergeComposed`
is clean: BOTH edits survive and `boundary_layout_child_disjoint` applies. `#guard`s evaluate the
`.layout.atoms` / `.children …` PROJECTIONS (decidable), the machine-checked non-vacuity teeth. -/

/-- A one-atom live graph at id `i` (a real leaf cell / layout fragment). -/
def liveAtom (i : AtomId) : DocGraph where
  atoms := fun j => if j = i then some Status.alive else none
  order := ∅
  fields := fun _ => ∅

/-- The two embedded child cells for the witnesses. -/
def cellA : CellId := 1
def cellB : CellId := 2

/-- Composed doc X: layout atom `100`; child `cellA` = leaf atom `200`. -/
def docX : ComposedDoc where
  layout := liveAtom 100
  children := fun c => if c = cellA then some (liveAtom 200) else none

/-- Composed doc Y: layout atom `101`; child `cellA` = leaf atom `201`; child `cellB` = leaf `300`. -/
def docY : ComposedDoc where
  layout := liveAtom 101
  children := fun c => if c = cellA then some (liveAtom 201)
                       else if c = cellB then some (liveAtom 300) else none

/-- A projection helper: the alive-status of atom `i` inside a child cell, or `none` if the cell or
atom is absent (decidable, so `#guard`-able over the function-fielded `DocGraph`). -/
def childAtom (d : ComposedDoc) (c : CellId) (i : AtomId) : Option Status :=
  match d.children c with
  | some g => g.atoms i
  | none   => none

-- (a) `mergeComposed` GENUINELY FIRES: the layout carries BOTH `100` and `101`, and child `cellA`
--     carries BOTH `200` and `201` (its two forks merged in ITS OWN AtomId space) — a real join,
--     not an identity. Child `cellB` (present only in Y) carries through.
#guard decide ((mergeComposed docX docY).layout.atoms 100 = some Status.alive)
#guard decide ((mergeComposed docX docY).layout.atoms 101 = some Status.alive)
#guard decide (childAtom (mergeComposed docX docY) cellA 200 = some Status.alive)
#guard decide (childAtom (mergeComposed docX docY) cellA 201 = some Status.alive)
#guard decide (childAtom (mergeComposed docX docY) cellB 300 = some Status.alive)
-- The layout has NO atom `200`/`201` (those live in the CHILD's space, never the layout) — the
-- disjointness is observable: a child atom never leaks into the layout coordinate.
#guard decide ((mergeComposed docX docY).layout.atoms 200 = none)
#guard decide ((mergeComposed docX docY).layout.atoms 201 = none)

/-! ### (b) The two-author boundary scenario — A edits child `cellA`, B edits the layout, clean. -/

/-- The common base: layout atom `100`; child `cellA` = leaf atom `200`. -/
def base : ComposedDoc where
  layout := liveAtom 100
  children := fun c => if c = cellA then some (liveAtom 200) else none

/-- Author B's edit — CONFINED TO THE LAYOUT: adds layout atom `101` (children untouched). -/
def authorB : ComposedDoc where
  layout := DocMerge.merge (liveAtom 100) (liveAtom 101)
  children := base.children

/-- Author A's edit — CONFINED TO CHILD `cellA`: adds child atom `201` (layout + other children
untouched). -/
def authorA : ComposedDoc where
  layout := base.layout
  children := fun c => if c = cellA then some (DocMerge.merge (liveAtom 200) (liveAtom 201))
                       else base.children c

/-- The composed merge of the two confined edits (A's child edit ⊔ B's layout edit). -/
def authorMerge : ComposedDoc := mergeComposed authorB authorA

-- BOTH edits survive with NO cross-conflict: the layout has A's untouched `100` + B's new `101`;
-- child `cellA` has the base `200` + A's new `201` — disjoint spaces, clean union.
#guard decide (authorMerge.layout.atoms 100 = some Status.alive)   -- base layout atom kept
#guard decide (authorMerge.layout.atoms 101 = some Status.alive)   -- B's layout edit survived
#guard decide (childAtom authorMerge cellA 200 = some Status.alive) -- base child atom kept
#guard decide (childAtom authorMerge cellA 201 = some Status.alive) -- A's child edit survived
-- The layout coordinate is UNPERTURBED by A's child edit (no `201` leaked into the layout).
#guard decide (authorMerge.layout.atoms 201 = none)

/-- **`author_scenario_boundary` (NON-VACUITY of the boundary lemma on a concrete pair).** The two
confined edits above satisfy `boundary_layout_child_disjoint`: B is confined to the layout, A to child
`cellA`, and the merge separates by component. This instantiates the load-bearing theorem on a REAL
two-author trace — the boundary lemma is not vacuous. -/
theorem author_scenario_boundary :
    (mergeComposed authorB authorA).layout = DocMerge.merge authorB.layout base.layout ∧
    (mergeComposed authorB authorA).children cellA
      = childJoin (base.children cellA) (authorA.children cellA) ∧
    (∀ c', c' ≠ cellA → (mergeComposed authorB authorA).children c' = base.children c') := by
  apply boundary_layout_child_disjoint (o := base) (dA := authorB) (dB := authorA) cellA
  · rfl
  · rfl
  · intro c' hc'
    show (if c' = cellA then _ else base.children c') = base.children c'
    rw [if_neg hc']

/-! ### The CONTRAST tooth — WITHIN a single component a clash CAN occur (so the boundary is real).

The boundary lemma rules out cross-component conflict. To show it is saying something — that it rules
out what CAN happen within ONE component — we exhibit two composed docs whose SAME child cell holds a
concurrent single-valued field clash (the single-cell `field_not_iconfluent`, DocMerge:529), lifted
into the family. Cross-component: never; same-component: possible. THAT gap is the boundary lemma. -/

/-- A composed doc whose child `cellA` assigns `{0}` to field `0`. -/
def clashX : ComposedDoc where
  layout := liveAtom 100
  children := fun c => if c = cellA then some ⟨fun _ => none, ∅, fun _ => {0}⟩ else none

/-- A composed doc whose child `cellA` assigns `{1}` to field `0` — a concurrent clash on the SAME cell. -/
def clashY : ComposedDoc where
  layout := liveAtom 100
  children := fun c => if c = cellA then some ⟨fun _ => none, ∅, fun _ => {1}⟩ else none

/-- The merged child `cellA`'s field `0`, if present. -/
def clashField (d : ComposedDoc) : Finset Val :=
  match d.children cellA with
  | some g => g.fields 0
  | none   => ∅

/-- **`same_cell_field_clash_possible` (the CONTRAST).** Two composed docs editing the SAME child cell
`cellA` at the SAME field DO clash — the merged child holds TWO values `{0,1}` at name `0`. This is the
single-cell `field_not_iconfluent` inside one family component. It shows the boundary lemma is
non-vacuous: WITHIN a component a clash is possible, so "ACROSS components, never" is a real theorem. -/
theorem same_cell_field_clash_possible :
    (clashField (mergeComposed clashX clashY)) = ({0, 1} : Finset Val) ∧
    2 ≤ (clashField (mergeComposed clashX clashY)).card := by
  have h : clashField (mergeComposed clashX clashY) = ({0, 1} : Finset Val) := by decide
  exact ⟨h, by rw [h]; decide⟩

-- The clash is observable on the projection too (machine-checked non-vacuity of the contrast).
#guard decide (clashField (mergeComposed clashX clashY) = ({0, 1} : Finset Val))

/-! ### NON-VACUITY at the `ConflictAt` level — a real conflict WITHIN a cell, none ACROSS authors. -/

/-- A composed doc whose child `cellA` is fork A of the DocMerge conflict witness (`base` merged with
`Connect p 1`). -/
def conflictComposedX : ComposedDoc where
  layout := liveAtom 100
  children := fun c => if c = cellA then some (DocMerge.merge DocMerge.base DocMerge.forkA) else none

/-- A composed doc whose child `cellA` is fork B (`Connect p 2`) — a CONCURRENT edit on the SAME cell. -/
def conflictComposedY : ComposedDoc where
  layout := liveAtom 100
  children := fun c => if c = cellA then some DocMerge.forkB else none

/-- **`composed_child_can_conflict` (the theorem rules out something REAL).** Merging two concurrent
edits to the SAME child cell `cellA` yields, in that cell's coordinate, DocMerge's genuine
`conflictGraph` — a live `ConflictAt` (`DocMerge.merge_has_conflict`, the transitive antichain
`1 ↮ 2`). So a `ConflictAt` DOES arise within a single family component; `boundary_no_joint_conflict`
ruling out a CROSS-author (layout-vs-child) conflict is therefore non-vacuous. -/
theorem composed_child_can_conflict :
    ∃ g, (mergeComposed conflictComposedX conflictComposedY).children cellA = some g ∧
         ConflictAt g DocMerge.pId DocMerge.aId DocMerge.bId :=
  -- Everything is concrete: the child coordinate reduces DEFINITIONALLY to `conflictGraph`
  -- (childJoin (some (merge base forkA)) (some forkB) = some (merge (merge base forkA) forkB)).
  ⟨DocMerge.conflictGraph, rfl, DocMerge.merge_has_conflict⟩

/-- **`author_scenario_conflict_free` (the two confined edits produce NO conflict).** The two-author
boundary scenario (`authorB` edits the layout, `authorA` edits child `cellA`) merges to a document
with NO `ConflictAt` in its layout coordinate at all — the merged layout has no order-edges, so no two
atoms can be a reached-from-`p` antichain. The confined layout edit and child edit are conflict-free,
exactly the Rust `layout_edit_and_child_edit_do_not_conflict` (composition.rs:1342). -/
theorem author_scenario_conflict_free :
    ¬ ∃ p x y, ConflictAt authorMerge.layout p x y := by
  have hord : authorMerge.layout.order = ∅ := by decide
  rintro ⟨p, x, y, hxy, _, _, hpx, hpy, _, _⟩
  have hno : ∀ z, (p, z) ∉ authorMerge.layout.order := by
    intro z hz; rw [hord] at hz; simp at hz
  have hpx' : p = x := reaches_stuck_of_no_out hno hpx
  have hpy' : p = y := reaches_stuck_of_no_out hno hpy
  exact hxy (hpx' ▸ hpy')

/-! ## 8. Axiom hygiene — every load-bearing keystone is kernel-clean
(⊆ {propext, Classical.choice, Quot.sound}). -/

#assert_axioms childJoin_comm
#assert_axioms childJoin_assoc
#assert_axioms childJoin_idem
#assert_axioms mergeComposed_comm
#assert_axioms mergeComposed_assoc
#assert_axioms mergeComposed_idem
#assert_axioms mergeComposed_total
#assert_axioms IncludesC.refl
#assert_axioms IncludesC.trans
#assert_axioms IncludesC.antisymm
#assert_axioms mergeComposed_includesC_left
#assert_axioms mergeComposed_includesC_right
#assert_axioms mergeComposed_least
#assert_axioms mergeComposed_is_lub
#assert_axioms mergeComposed_isPushout
#assert_axioms pushoutC_unique
#assert_axioms mergeComposed_layout_is_pushout
#assert_axioms mergeComposed_child_is_pushout
#assert_axioms boundary_layout_child_disjoint
#assert_axioms boundary_no_cross_perturbation
#assert_axioms boundary_no_joint_conflict
#assert_axioms composed_child_can_conflict
#assert_axioms author_scenario_conflict_free
#assert_axioms author_scenario_boundary
#assert_axioms same_cell_field_clash_possible

end Dregg2.Deos.DocMergeComposed

/-
# Dregg2.Deos.DocPatch — the PATCH-COMMUTATION law: INDEPENDENT additive patch ops COMMUTE (the
# Pijul patch-theory heart), each op is INCLUSION-MONOTONE in `⊑`, and APPLY IS MERGE-with-a-singleton.

`docs/deos/DOCUMENT-LANGUAGE.md` §2.2 ("patches commute whenever they touch disjoint parts of the
graph"). Differential target: the Rust crate `dregg-doc` (`/Users/ember/dev/breadstuffs/dregg-doc/src/
{patch,graph}.rs`), built ON TOP OF the faithful merge-algebra `Dregg2.Deos.DocMerge`.

**The Pijul thesis, made literal.** patch.rs:6–9: *"The forward graph ops (`Add`/`Delete`/`Connect`)
are additive: they add a vertex, add a tombstone, or add an order-edge. Nothing is ever subtracted.
This is the whole reason patches commute (when they touch disjoint parts of the graph)."* This file
proves exactly that sentence: the three additive op effects, each modelled as a `DocGraph → DocGraph`,

  1. COMMUTE when they touch disjoint parts of the graph (`*_comm` theorems), and even
     unconditionally for the two structurally-disjoint-by-construction cases (atom-vs-edge,
     edge-vs-atom — they write DIFFERENT struct fields),
  2. are each INFLATIONARY in the `Dregg2.Deos.DocMerge.Includes` order `⊑` (the monotonicity SPINE —
     the reason commutation holds: each op only GROWS the graph, even `tombstone`, whose `alive→dead`
     is UP in the `Status.le` order `⊑` uses), and
  3. ARE merge-with-a-singleton: `addEdge e g = merge g (singletonEdge e)`, `tombstone i g =
     merge g (singletonDead i)` — so a patch application IS a `merge`, and the op effects INHERIT
     `merge`'s comm/assoc/idem from `DocMerge`. This is the deep unification: "apply is merge with a
     small graph", and it is WHY commutation is not a coincidence — it is `merge_comm` specialised.

**The faithful op effects (the atoms of the patch grammar, `patch.rs::Op` / `graph.rs`):**

  * `addAtom i g` — `Op::Add`'s vertex half = `graph.rs::insert_atom` (graph.rs:184–186): `entry(id)
    .or_insert(...)` — an IDEMPOTENT insert that does NOT overwrite. We model it as: set `atoms i` to
    `some .alive` only if ABSENT (`none`); leave a present atom (alive OR dead) UNTOUCHED. This is the
    `or_insert` "never resurrects a tombstone, never overwrites" (patch.rs:181–183) faithfully — so
    `addAtom` is genuinely idempotent and never un-tombstones.
  * `addEdge (a,b) g` — `Op::Connect` / the edge half of `Op::Add` = `graph.rs::connect`
    (graph.rs:208–213): `Finset.insert (a,b) g.order`. (We model the general edge insert; the
    self-loop drop `from == to` (graph.rs:209–211) is a separate refinement — see `addEdge` doc.)
  * `tombstone i g` — `Op::Delete` = `graph.rs::tombstone` (graph.rs:191–195): if `atoms i` is
    present, set its status to `.dead`; a MISSING atom is ignored ("you can only delete what some add
    introduced"). Monotone `alive→dead`; a dead atom stays dead.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); NO `sorry`/`native_decide`.
Verified with `lake build Dregg2.Deos.DocPatch`. Differential: `dregg-doc/src/{patch,graph}.rs`.
-/
import Dregg2.Deos.DocMerge

namespace Dregg2.Deos.DocPatch

open Dregg2.Deos.DocMerge

/-! ## 1. The additive op effects — the atoms of the patch grammar (`patch.rs::Op`, `graph.rs`). -/

/-- **`addAtom i g`** — the vertex half of `Op::Add` = `graph.rs::insert_atom` (graph.rs:184–186):
`self.atoms.entry(id).or_insert(atom)`. An IDEMPOTENT insert: if `i` is ABSENT (`none`) it becomes
`some .alive`; if `i` is already PRESENT (alive OR dead) it is left UNTOUCHED — the `or_insert`
"never resurrects a tombstone, never overwrites content/provenance" (patch.rs:181–183). Only the
`atoms` field of the struct is touched; `order`/`fields` carry through. -/
def addAtom (i : AtomId) (g : DocGraph) : DocGraph where
  atoms := fun j => if j = i then (match g.atoms i with
                                   | none => some .alive
                                   | some v => some v)
                    else g.atoms j
  order := g.order
  fields := g.fields

/-- **`addEdge e g`** — `Op::Connect` / the edge half of `Op::Add` = `graph.rs::connect`
(graph.rs:208–213): `Finset.insert e g.order`. Additive + idempotent (a `Finset.insert`). Only the
`order` field is touched. (The Rust `connect` additionally DROPS self-loops `from == to`
(graph.rs:209–211); we model the general edge insert — every concrete witness here uses `a ≠ b`, so
this is the faithful effect on the non-degenerate edges patches actually carry.) -/
def addEdge (e : AtomId × AtomId) (g : DocGraph) : DocGraph where
  atoms := g.atoms
  order := insert e g.order
  fields := g.fields

/-- **`tombstone i g`** — `Op::Delete` = `graph.rs::tombstone` (graph.rs:191–195): `if let Some(a) =
self.atoms.get_mut(&id) { a.status = Status::Dead }`. If `i` is PRESENT, its status becomes `.dead`;
a MISSING atom (`none`) is IGNORED ("you can only delete what some add introduced", graph.rs:189).
Monotone `alive→dead`; a dead atom stays dead. Only the `atoms` field is touched. -/
def tombstone (i : AtomId) (g : DocGraph) : DocGraph where
  atoms := fun j => if j = i then (match g.atoms i with
                                   | none => none
                                   | some _ => some .dead)
                    else g.atoms j
  order := g.order
  fields := g.fields

/-! ### Projection lemmas — what each op writes (and, crucially, LEAVES). -/

@[simp] theorem addAtom_order (i : AtomId) (g : DocGraph) : (addAtom i g).order = g.order := rfl
@[simp] theorem addAtom_fields (i : AtomId) (g : DocGraph) (n : Name) :
    (addAtom i g).fields n = g.fields n := rfl
@[simp] theorem addEdge_atoms (e : AtomId × AtomId) (g : DocGraph) (j : AtomId) :
    (addEdge e g).atoms j = g.atoms j := rfl
@[simp] theorem addEdge_order (e : AtomId × AtomId) (g : DocGraph) :
    (addEdge e g).order = insert e g.order := rfl
@[simp] theorem addEdge_fields (e : AtomId × AtomId) (g : DocGraph) (n : Name) :
    (addEdge e g).fields n = g.fields n := rfl
@[simp] theorem tombstone_order (i : AtomId) (g : DocGraph) : (tombstone i g).order = g.order := rfl
@[simp] theorem tombstone_fields (i : AtomId) (g : DocGraph) (n : Name) :
    (tombstone i g).fields n = g.fields n := rfl

/-- `addAtom` at the target id: present stays, absent becomes alive. -/
theorem addAtom_atoms_self (i : AtomId) (g : DocGraph) :
    (addAtom i g).atoms i = (match g.atoms i with | none => some .alive | some v => some v) := by
  simp only [addAtom, if_true]

/-- `addAtom` off-target is the identity. -/
@[simp] theorem addAtom_atoms_other {i j : AtomId} (h : j ≠ i) (g : DocGraph) :
    (addAtom i g).atoms j = g.atoms j := by simp only [addAtom, if_neg h]

/-- `tombstone` off-target is the identity. -/
@[simp] theorem tombstone_atoms_other {i j : AtomId} (h : j ≠ i) (g : DocGraph) :
    (tombstone i g).atoms j = g.atoms j := by simp only [tombstone, if_neg h]

/-! ## 2. THE COMMUTATION THEOREMS — independent additive ops COMMUTE (`DOCUMENT-LANGUAGE.md` §2.2,
patch.rs:6–9). The general shape: ops touching DISJOINT parts of the graph commute. -/

/-- **`addAtom_addAtom_comm` (atom-inserts commute, UNCONDITIONALLY).** `addAtom i (addAtom j g) =
addAtom j (addAtom i g)` for ALL `i j` — no disjointness side-condition needed: two DIFFERENT ids
touch different keys; the SAME id is idempotent (`or_insert` is a no-op the second time). Proven by
`funext` on `atoms` with a case split on `j = i`. -/
theorem addAtom_addAtom_comm (i j : AtomId) (g : DocGraph) :
    addAtom i (addAtom j g) = addAtom j (addAtom i g) := by
  apply DocGraph.ext
  · intro k
    by_cases hki : k = i <;> by_cases hkj : k = j
    · -- k = i = j: same id, idempotent both sides.
      subst hki; subst hkj
      simp only [addAtom_atoms_self]
    · subst hki
      rw [addAtom_atoms_self, addAtom_atoms_other hkj, addAtom_atoms_other (by simpa using hkj),
        addAtom_atoms_self]
    · subst hkj
      rw [addAtom_atoms_other (by simpa using hki), addAtom_atoms_self, addAtom_atoms_self,
        addAtom_atoms_other (by simpa using hki)]
    · rw [addAtom_atoms_other hki, addAtom_atoms_other hkj, addAtom_atoms_other hkj,
        addAtom_atoms_other hki]
  · simp only [addAtom_order]
  · intro n; simp only [addAtom_fields]

/-- **`addEdge_addEdge_comm` (edge-inserts commute, UNCONDITIONALLY).** `addEdge e (addEdge f g) =
addEdge f (addEdge e g)` for ALL edges `e f` — it is `Finset.Insert.comm` on the order set. -/
theorem addEdge_addEdge_comm (e f : AtomId × AtomId) (g : DocGraph) :
    addEdge e (addEdge f g) = addEdge f (addEdge e g) := by
  apply DocGraph.ext
  · intro k; simp only [addEdge_atoms]
  · simp only [addEdge_order, Finset.insert_comm]
  · intro n; simp only [addEdge_fields]

/-- **`addAtom_addEdge_comm` (an atom-insert and an edge-insert commute, UNCONDITIONALLY).** They
touch DIFFERENT struct fields (`atoms` vs `order`) — the structurally-disjoint case `§2.2` calls out.
No side-condition. -/
theorem addAtom_addEdge_comm (i : AtomId) (e : AtomId × AtomId) (g : DocGraph) :
    addAtom i (addEdge e g) = addEdge e (addAtom i g) := by
  apply DocGraph.ext
  · intro k
    by_cases hki : k = i
    · subst hki; simp only [addEdge_atoms, addAtom_atoms_self]
    · simp only [addAtom_atoms_other hki, addEdge_atoms]
  · simp only [addAtom_order, addEdge_order]
  · intro n; simp only [addAtom_fields, addEdge_fields]

/-- **`tombstone_addEdge_comm` (a tombstone and an edge-insert commute, UNCONDITIONALLY).** Different
struct fields (`atoms` vs `order`). -/
theorem tombstone_addEdge_comm (i : AtomId) (e : AtomId × AtomId) (g : DocGraph) :
    tombstone i (addEdge e g) = addEdge e (tombstone i g) := by
  apply DocGraph.ext
  · intro k
    by_cases hki : k = i
    · subst hki; simp only [addEdge_atoms, tombstone]
    · simp only [tombstone_atoms_other hki, addEdge_atoms]
  · simp only [tombstone_order, addEdge_order]
  · intro n; simp only [tombstone_fields, addEdge_fields]

/-- **`addAtom_tombstone_comm` (an atom-insert and a tombstone at DISJOINT ids commute).** For `i ≠ j`
they touch different keys, so they commute. (At the SAME id they do NOT: `addAtom (tombstone i g)`
leaves the dead atom — `or_insert` no-op — while `tombstone (addAtom i g)` kills the freshly-inserted
atom, a genuine DIFFERENCE. So this op-pair commutes EXACTLY on disjoint ids — the precise §2.2
"disjoint parts" boundary, witnessed in §5.) -/
theorem addAtom_tombstone_comm {i j : AtomId} (h : i ≠ j) (g : DocGraph) :
    addAtom i (tombstone j g) = tombstone j (addAtom i g) := by
  apply DocGraph.ext
  · intro k
    by_cases hki : k = i
    · subst hki
      simp only [addAtom, tombstone, if_neg h]
    · by_cases hkj : k = j
      · subst hkj
        simp only [addAtom, tombstone, if_neg (Ne.symm h)]
      · simp only [addAtom, tombstone, if_neg hki, if_neg hkj]
  · simp only [addAtom_order, tombstone_order]
  · intro n; simp only [addAtom_fields, tombstone_fields]

/-- **`tombstone_tombstone_comm` (tombstones commute, UNCONDITIONALLY).** Same id: idempotent
(`alive→dead→dead`); different ids: different keys. Tombstoning is monotone so order never matters. -/
theorem tombstone_tombstone_comm (i j : AtomId) (g : DocGraph) :
    tombstone i (tombstone j g) = tombstone j (tombstone i g) := by
  apply DocGraph.ext
  · intro k
    by_cases hki : k = i <;> by_cases hkj : k = j
    · subst hki; subst hkj; simp only [tombstone]
    · subst hki; simp only [tombstone, if_neg hkj]
    · subst hkj; simp only [tombstone, if_neg hki]
    · simp only [tombstone, if_neg hki, if_neg hkj]
  · simp only [tombstone_order]
  · intro n; simp only [tombstone_fields]

/-! ## 3. THE MONOTONICITY SPINE — each op is INFLATIONARY in `⊑` (the REASON commutation holds). -/

/-- **`addAtom_inflationary`.** `g ⊑ addAtom i g`: an atom-insert only GROWS the graph. On a present
atom the value is UNTOUCHED (`Status.le_refl`); on the inserted atom there was nothing to dominate.
Order/fields are unchanged (`Finset.Subset.refl`). -/
theorem addAtom_inflationary (i : AtomId) (g : DocGraph) : g ⊑ addAtom i g := by
  refine ⟨?_, ?_, ?_⟩
  · intro j v hv
    by_cases hji : j = i
    · subst hji; rw [addAtom_atoms_self, hv]; exact ⟨v, rfl, Status.le_refl v⟩
    · rw [addAtom_atoms_other hji]; exact ⟨v, hv, Status.le_refl v⟩
  · rw [addAtom_order]
  · intro n; rw [addAtom_fields]

/-- **`addEdge_inflationary`.** `g ⊑ addEdge e g`: an edge-insert only grows `order`
(`Finset.subset_insert`); atoms/fields unchanged. -/
theorem addEdge_inflationary (e : AtomId × AtomId) (g : DocGraph) : g ⊑ addEdge e g := by
  refine ⟨?_, ?_, ?_⟩
  · intro j v hv; rw [addEdge_atoms]; exact ⟨v, hv, Status.le_refl v⟩
  · rw [addEdge_order]; exact Finset.subset_insert _ _
  · intro n; rw [addEdge_fields]

/-- **`tombstone_inflationary`.** `g ⊑ tombstone i g`: tombstoning is UP in `⊑` because `alive→dead`
is UP in the `Status.le` order `Includes` uses (`alive ≤ dead`). A present atom advances to `.dead`
(`Status.le` to dead is always `True` for both alive and dead sources); a missing atom stays missing.
This is the audit-relevant point: even the DESTRUCTIVE-looking tombstone is inclusion-MONOTONE,
because the document order treats liveness as `alive ≤ dead`. Order/fields unchanged. -/
theorem tombstone_inflationary (i : AtomId) (g : DocGraph) : g ⊑ tombstone i g := by
  refine ⟨?_, ?_, ?_⟩
  · intro j v hv
    by_cases hji : j = i
    · subst hji
      refine ⟨.dead, ?_, ?_⟩
      · simp only [tombstone, if_true, hv]
      · cases v <;> trivial
    · rw [tombstone_atoms_other hji]; exact ⟨v, hv, Status.le_refl v⟩
  · rw [tombstone_order]
  · intro n; rw [tombstone_fields]

/-! ## 4. APPLY-IS-MERGE — the deep unification: a patch op IS `merge` with a small graph.

Adding an edge / a dead atom is the SAME as merging in a singleton graph carrying just that edge /
that dead status. So a patch application IS a `merge` (`DocMerge.merge`) — and the op effects INHERIT
`merge`'s comm/assoc/idem. This is WHY the commutation theorems above are not a coincidence: they are
`merge_comm` specialised to singleton graphs. (`addAtom` is `merge` with an atom-singleton EXCEPT on
an already-present id, where `or_insert`'s no-op DIVERGES from the status-join — so the clean
apply-as-merge bridge is the two cases that touch `none`-or-pure-`order`: see `addEdge_is_merge` and
`tombstone_is_merge_on_present`.) -/

/-- The singleton graph carrying just the edge `e` (`DocGraph::new` + one `connect`). -/
def singletonEdge (e : AtomId × AtomId) : DocGraph where
  atoms := fun _ => none
  order := {e}
  fields := fun _ => ∅

/-- The singleton graph carrying just a DEAD atom at `i` (`DocGraph::new` + an insert + a tombstone). -/
def singletonDead (i : AtomId) : DocGraph where
  atoms := fun j => if j = i then some .dead else none
  order := ∅
  fields := fun _ => ∅

/-- **`addEdge_is_merge` (APPLY IS MERGE — the edge case, the clean bridge).** `addEdge e g =
merge g (singletonEdge e)`: inserting an order-edge is EXACTLY merging in the edge-singleton. So a
`Connect` patch application IS a `merge`, and `addEdge_addEdge_comm` is `merge_comm` + `merge_assoc`
specialised. The deep unification, stated. -/
theorem addEdge_is_merge (e : AtomId × AtomId) (g : DocGraph) :
    addEdge e g = merge g (singletonEdge e) := by
  apply DocGraph.ext
  · intro j; rw [addEdge_atoms, merge_atoms]; simp only [singletonEdge, atomJoin]
    cases g.atoms j <;> rfl
  · rw [addEdge_order, merge_order]; simp only [singletonEdge]
    rw [Finset.union_comm, Finset.insert_eq]
  · intro n; rw [addEdge_fields, merge_fields]; simp only [singletonEdge, Finset.union_empty]

/-- **`tombstone_is_merge_on_present` (APPLY IS MERGE — the tombstone case, on a present atom).**
When `i` is PRESENT, `tombstone i g = merge g (singletonDead i)`: the Dead-wins `Status.join` of
the singleton's `.dead` against `g`'s present status gives `.dead` — exactly the tombstone. (On an
ABSENT id the bridge would INTRODUCE the atom as dead, whereas `tombstone` IGNORES a missing id — the
faithful divergence, which is why this bridge carries the `present` hypothesis.) The other direction
of the deep unification: a `Delete` on what some add introduced IS a `merge`. -/
theorem tombstone_is_merge_on_present (i : AtomId) (g : DocGraph) (hpres : g.atoms i ≠ none) :
    tombstone i g = merge g (singletonDead i) := by
  apply DocGraph.ext
  · intro j
    by_cases hji : j = i
    · subst hji
      rw [merge_atoms]; simp only [singletonDead, if_true, tombstone]
      cases hgi : g.atoms j with
      | none => exact absurd hgi hpres
      | some v => simp only [atomJoin, Status.join_dead_right]
    · rw [tombstone_atoms_other hji, merge_atoms]
      simp only [singletonDead, if_neg hji, atomJoin]
      cases g.atoms j <;> rfl
  · rw [tombstone_order, merge_order]; simp only [singletonDead, Finset.union_empty]
  · intro n; rw [tombstone_fields, merge_fields]; simp only [singletonDead, Finset.union_empty]

/-- **`addEdge_commutes_via_merge` (the unification PAYOFF, demonstrated).** The edge-commutation law
is RE-DERIVED purely from `addEdge_is_merge` + `merge_assoc`/`merge_comm` — showing the commutation is
the lattice join's commutativity in disguise, not an independent fact. -/
theorem addEdge_commutes_via_merge (e f : AtomId × AtomId) (g : DocGraph) :
    addEdge e (addEdge f g) = addEdge f (addEdge e g) := by
  rw [addEdge_is_merge, addEdge_is_merge, addEdge_is_merge (g := addEdge e g), addEdge_is_merge]
  rw [merge_assoc, merge_assoc, merge_comm (singletonEdge f) (singletonEdge e)]

/-! ## 5. NON-VACUITY teeth — concrete independent ops give the SAME result in both orders; the
SAME-id boundary genuinely DIFFERS (so the disjointness side-condition is load-bearing). -/

/-- A concrete base graph with atoms `1`, `2` alive (`DocGraph::new` + two inserts). -/
def g0 : DocGraph where
  atoms := fun j => if j = 1 ∨ j = 2 then some .alive else none
  order := ∅
  fields := fun _ => ∅

-- TWO INDEPENDENT EDGE INSERTS commute: adding (0,1) and (2,3) gives the SAME order set either way.
#guard (addEdge (0, 1) (addEdge (2, 3) g0)).order
       == (addEdge (2, 3) (addEdge (0, 1) g0)).order
#guard (addEdge (0, 1) (addEdge (2, 3) g0)).order
       == ({(0, 1), (2, 3)} : Finset (AtomId × AtomId))

-- TWO INDEPENDENT ATOM INSERTS at ids 3 and 4 commute on the (decidable) atom projections.
#guard (addAtom 3 (addAtom 4 g0)).atoms 3 == some Status.alive
#guard (addAtom 3 (addAtom 4 g0)).atoms 4 == some Status.alive
#guard (addAtom 4 (addAtom 3 g0)).atoms 3 == some Status.alive

-- addAtom is the `or_insert` NO-OP on a present id: re-adding `1` (already alive) leaves it alive.
#guard (addAtom 1 g0).atoms 1 == some Status.alive
-- addAtom NEVER resurrects a tombstone: adding an id that is already dead leaves it DEAD.
#guard (addAtom 1 (tombstone 1 g0)).atoms 1 == some Status.dead
-- tombstone IGNORES a missing id (no atom 5 in g0): stays absent.
#guard (tombstone 5 g0).atoms 5 == (none : Option Status)
-- tombstone is monotone: a live atom becomes dead.
#guard (tombstone 1 g0).atoms 1 == some Status.dead

-- THE SAME-ID BOUNDARY (why `addAtom_tombstone_comm` needs `i ≠ j`): at the SAME id the two orders
-- GENUINELY DIFFER — addAtom-then-tombstone kills the fresh atom (dead); tombstone-then-addAtom finds
-- nothing to delete then inserts (alive). A real non-commutation, exactly the §2.2 "disjoint" caveat.
#guard (tombstone 9 (addAtom 9 g0)).atoms 9 == some Status.dead
#guard (addAtom 9 (tombstone 9 g0)).atoms 9 == some Status.alive

-- addEdge IS merge with the edge-singleton (the apply-as-merge bridge, on the order projection).
#guard (addEdge (0, 1) g0).order == (merge g0 (singletonEdge (0, 1))).order

/-! ## 6. Axiom hygiene — every keystone kernel-clean (⊆ {propext, Classical.choice, Quot.sound}). -/

#assert_axioms addAtom_addAtom_comm
#assert_axioms addEdge_addEdge_comm
#assert_axioms addAtom_addEdge_comm
#assert_axioms tombstone_addEdge_comm
#assert_axioms addAtom_tombstone_comm
#assert_axioms tombstone_tombstone_comm
#assert_axioms addAtom_inflationary
#assert_axioms addEdge_inflationary
#assert_axioms tombstone_inflationary
#assert_axioms addEdge_is_merge
#assert_axioms tombstone_is_merge_on_present
#assert_axioms addEdge_commutes_via_merge

end Dregg2.Deos.DocPatch

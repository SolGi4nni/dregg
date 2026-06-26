/-
# Dregg2.Deos.DocMerge — the dreggverse DOCUMENT merge is the least-upper-bound JOIN (the
# colimit-by-union the Pijul pushout computes), with the FAITHFUL `Dead`-wins status join,
# TRANSITIVE-reachability conflicts, and a conflict as a FIRST-CLASS STATE.

`docs/deos/DOCUMENT-LANGUAGE.md` §2.1–2.4 + §4.4 RESEARCH. Differential target: the Rust crate
`dregg-doc` (`/Users/ember/dev/breadstuffs/dregg-doc/src/{graph,merge,content,atom}.rs`).

**Faithfulness note (this file was rebuilt to BE faithful, three audited gaps fixed).**

  1. **The status-join gap (severe).** An earlier draft modelled the atom store as a `Finset Atom`
     and unioned whole structs — which never applied the `Dead`-wins status join, so merging an id
     alive on one side and dead on the other produced a TWO-element set, a state the Rust
     `BTreeMap<AtomId, Atom>` cannot represent. THE FIX (here): the atom store is a KEYED MAP
     `AtomId → Option AtomVal` (the `BTreeMap`), and `merge` applies `Status.join` POINTWISE on
     shared ids — exactly `graph.rs::union_in_place`'s
     `.and_modify(|a| a.status = a.status.join(other.status)).or_insert(...)` (graph.rs:274–280).
     `merge_status_dead_wins` is the proof the old model could not even STATE.

  2. **The one-hop-conflict gap.** The earlier `OrderedBefore`/`ConflictAt` used one-hop edge
     membership; `content.rs::reachable` (content.rs:340) is a TRANSITIVE closure (reflexive on
     `start == target`, then a graph walk over `successors`). THE FIX: `Reaches g a b` is
     `Relation.ReflTransGen` of the edge relation `(·,·) ∈ g.order`; `ConflictAt` is MUTUAL
     non-reachability — a genuine transitive antichain matching `content.rs::walk` (content.rs:251).

  3. **The pushout overclaim.** The earlier docstrings called this "THE categorical pushout up to
     unique iso" — but the content is `Finset.union_subset`: the LATTICE JOIN / LUB. THE FIX: it is
     stated HONESTLY as "`merge a b` is the least upper bound (join) in the document inclusion order
     `⊑` — the colimit-by-union the pushout computes in the Pijul model." §9 then PROVES the
     categorical statement for the HONEST model — the THIN/PREORDER category of document states under
     `⊑`: there `merge a b` IS the pushout of any span `a ⊑← c →⊑ b`, unique up to unique iso, which
     in a poset degenerates to unique up to EQUALITY (the only isos are identities, by antisymmetry of
     `⊑`). The remaining residual (NAMED, not built): the FULL LABELLED patch category `P` whose
     MORPHISMS are patches (not mere inclusions) — a larger, non-thin category — and its functoriality.

**The content-abstraction (why dropping `payload` is FAITHFUL, not a cheat).** The merge never
inspects an atom's content or provenance: `union_in_place` JOINS `status` and, for an already-present
id, KEEPS the existing entry untouched (`and_modify` only touches `status`; graph.rs:277). So the
merge-observable value of an atom is JUST its `status`. Content + provenance are bound by the
COMMITMENT layer (`commit.rs`/`substrate.rs`), NOT the merge-algebra — so `AtomVal := Status` is
exactly what `merge` observes. This also removes the spurious content-addressing invariant the
old `payload`-carrying model needed to prove `atomJoin` commutative.

**The model, faithful to `dregg-doc`:**
  * `DocGraph` — `atoms : AtomId → Option AtomVal` (the keyed `BTreeMap`; ≤1 status per id BY
    CONSTRUCTION), `order : Finset (AtomId × AtomId)` (the edge set), `fields : Name → Finset Val`
    (the keyed single-valued store). (`graph.rs::DocGraph`.)
  * `merge` — pointwise: atoms join by `Option`-lifted `Status.join` (DEAD WINS, the real
    `union_in_place`), order ∪, fields ∪. (`merge.rs` = `graph.rs::union_in_place`.)
  * **THE JOIN LAWS**, now about the REAL status-joining merge: `merge_comm`, `merge_assoc`,
    `merge_idem`, `merge_total`. The status-join is genuinely exercised (`merge_status_dead_wins`).
  * **THE UNIVERSAL PROPERTY (as a lattice join, honestly):** `merge_is_lub` — `merge a b` is the
    least graph including both legs in the inclusion order `⊑` (`merge_includes_left/right` are the
    cocone legs; `merge_least` is leastness). The colimit-by-union the pushout computes.
  * **CONFLICT-AS-STATE.** `ConflictAt` — two distinct LIVE atoms after a shared `p` that are
    mutually UN-`Reaches`able (a transitive antichain, matching `content.rs::walk`).
    `merge_has_conflict` exhibits a concrete two-fork conflict that is a WELL-FORMED `DocGraph`
    (not a failure); `resolve_collapses` — an additive `Connect` makes one reach the other, removing
    the antichain, and is additive (`g ⊑ resolved`).
  * **THE TWO-REGIME SPLIT** (§2.4) connected to `Confluence.IConfluent`: `prose_iconfluent`
    (grow-only liveness survives merge) vs `field_not_iconfluent` (a single-valued field clashes —
    a constructed pair whose merge holds two values at one name).

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}).
Verified with `lake build Dregg2.Deos.DocMerge`. Differential: `dregg-doc/src/{merge,graph,content,atom}.rs`.
-/
import Dregg2.Confluence
import Dregg2.Tactics
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Logic.Relation

namespace Dregg2.Deos.DocMerge

/-! ## 1. The Pijul graph-of-atoms — faithful to `graph.rs::DocGraph` (keyed atom map). -/

/-- An atom id (`atom.rs::AtomId`); opaque. `root` is the start-of-document sentinel. -/
abbrev AtomId := Nat

/-- The reserved start-of-document sentinel (`AtomId::ROOT`). -/
def root : AtomId := 0

/-- Liveness (`atom.rs::Status`). Monotone `Alive → Dead`; the merge join is "Dead wins". -/
inductive Status where
  | alive
  | dead
deriving DecidableEq, Repr

/-- The monotone status join (`atom.rs::Status::join`, atom.rs:114): `Dead` absorbs `Alive`. -/
def Status.join : Status → Status → Status
  | .alive, .alive => .alive
  | _, _ => .dead

@[simp] theorem Status.join_alive_alive : Status.join .alive .alive = .alive := rfl
@[simp] theorem Status.join_dead_left (s : Status) : Status.join .dead s = .dead := rfl
@[simp] theorem Status.join_dead_right (s : Status) : Status.join s .dead = .dead := by
  cases s <;> rfl

theorem Status.join_comm (a b : Status) : Status.join a b = Status.join b a := by
  cases a <;> cases b <;> rfl

theorem Status.join_assoc (a b c : Status) :
    Status.join (Status.join a b) c = Status.join a (Status.join b c) := by
  cases a <;> cases b <;> cases c <;> rfl

@[simp] theorem Status.join_idem (a : Status) : Status.join a a = a := by cases a <;> rfl

/-- The monotone status order `alive ≤ dead` (`atom.rs`: an atom only travels `Alive → Dead`).
This is the order the document-inclusion `⊑` uses on a shared atom: `h`'s status is "at least as
advanced" as `g`'s. The status-join is its LUB. -/
def Status.le : Status → Status → Prop
  | .alive, _ => True
  | .dead, .dead => True
  | .dead, .alive => False

@[simp] theorem Status.le_refl (a : Status) : Status.le a a := by cases a <;> trivial
@[simp] theorem Status.alive_le (a : Status) : Status.le .alive a := trivial

theorem Status.le_trans {a b c : Status} : Status.le a b → Status.le b c → Status.le a c := by
  cases a <;> cases b <;> cases c <;> simp [Status.le]

/-- `a ≤ join a b` — the join is an upper bound for the left status (DEAD-wins makes it so). -/
theorem Status.le_join_left (a b : Status) : Status.le a (Status.join a b) := by
  cases a <;> cases b <;> simp [Status.le, Status.join]

/-- `b ≤ join a b` — the join is an upper bound for the right status. -/
theorem Status.le_join_right (a b : Status) : Status.le b (Status.join a b) := by
  cases a <;> cases b <;> simp [Status.le, Status.join]

/-- `join a b` is the LEAST upper bound: any common upper bound `c` dominates it. -/
theorem Status.join_le {a b c : Status} (ha : Status.le a c) (hb : Status.le b c) :
    Status.le (Status.join a b) c := by
  cases a <;> cases b <;> cases c <;> simp_all [Status.le, Status.join]

/-- An atom's MERGE-OBSERVABLE value (`graph.rs::Atom` minus id/content/provenance, which `merge`
never reads). The merge JOINS status and otherwise keeps the existing entry, so the observable an
atom contributes to a merge IS its `status` — content + provenance live in the COMMITMENT layer
(`commit.rs`/`substrate.rs`), not the merge-algebra. So `AtomVal := Status` is faithful to what
`union_in_place` observes (graph.rs:274–280 reads only `status`). -/
abbrev AtomVal := Status

/-- The `Option`-lifted atom join — exactly `graph.rs::union_in_place` on the atom map
(graph.rs:274–280): on a SHARED id both present, the status JOINS (Dead wins). On an id present on
one side only, that side's value carries. With `AtomVal := Status` this is cleanly commutative /
associative / idempotent with NO content-addressing invariant. -/
def atomJoin : Option AtomVal → Option AtomVal → Option AtomVal
  | some a, some b => some (Status.join a b)
  | some a, none   => some a
  | none,   some b => some b
  | none,   none   => none

/-- A field name (`graph.rs::fields` key). -/
abbrev Name := Nat
/-- A field value (`graph.rs::FieldAssign::value`). -/
abbrev Val := Nat

/-- **`DocGraph`** — faithful to `graph.rs::DocGraph`: a KEYED atom map (≤1 entry per id by
construction — the `BTreeMap`), the order-edge set, and a KEYED single-valued field store
(name ↦ the set of concurrently-assigned values; `graph.rs::fields : BTreeMap<String, Vec<…>>`). -/
structure DocGraph where
  /-- The atom map (`graph.rs::atoms`): id ↦ its merge-observable value, or `none` if absent. -/
  atoms : AtomId → Option AtomVal
  /-- Order-edges `(a, b)` = "`a` before `b`" (`graph.rs::edges`). -/
  order : Finset (AtomId × AtomId)
  /-- Single-valued fields (`graph.rs::fields`): name ↦ the set of assigned values. ≥2 ⇒ a clash. -/
  fields : Name → Finset Val

/-- Componentwise extensionality for `DocGraph` (the structure has a function `atoms`/`fields`
field, so equality reduces to `funext` on those + the `order` Finset). -/
theorem DocGraph.ext {a b : DocGraph}
    (hatoms : ∀ i, a.atoms i = b.atoms i)
    (horder : a.order = b.order)
    (hfields : ∀ n, a.fields n = b.fields n) : a = b := by
  cases a; cases b
  simp only [DocGraph.mk.injEq]
  exact ⟨funext hatoms, horder, funext hfields⟩

/-! ## 2. `merge` — the componentwise join (the colimit-by-union, `merge.rs` = `union_in_place`). -/

/-- **`merge a b`** — `merge.rs::merge` = `graph.rs::union_in_place`: atoms join pointwise by
`atomJoin` (the REAL Dead-wins status join), order-edges union, field-value sets union. Total by
construction. -/
def merge (a b : DocGraph) : DocGraph where
  atoms := fun i => atomJoin (a.atoms i) (b.atoms i)
  order := a.order ∪ b.order
  fields := fun n => a.fields n ∪ b.fields n

@[simp] theorem merge_atoms (a b : DocGraph) (i : AtomId) :
    (merge a b).atoms i = atomJoin (a.atoms i) (b.atoms i) := rfl
@[simp] theorem merge_order (a b : DocGraph) : (merge a b).order = a.order ∪ b.order := rfl
@[simp] theorem merge_fields (a b : DocGraph) (n : Name) :
    (merge a b).fields n = a.fields n ∪ b.fields n := rfl

/-! ### `atomJoin` is the commutative-associative-idempotent join the laws ride on (now trivial). -/

theorem atomJoin_comm (x y : Option AtomVal) : atomJoin x y = atomJoin y x := by
  cases x <;> cases y <;> simp only [atomJoin, Status.join_comm]

theorem atomJoin_assoc (x y z : Option AtomVal) :
    atomJoin (atomJoin x y) z = atomJoin x (atomJoin y z) := by
  cases x <;> cases y <;> cases z <;> simp only [atomJoin, Status.join_assoc]

@[simp] theorem atomJoin_idem (x : Option AtomVal) : atomJoin x x = x := by
  cases x <;> simp only [atomJoin, Status.join_idem]

/-! ## 3. THE JOIN LAWS — about the REAL status-joining merge (not a struct-union). -/

/-- **`merge_comm` (COMMUTATIVITY).** `merge a b = merge b a`: order independent merge. The atoms
field needs `funext` + `atomJoin_comm`; order/fields need `Finset.union_comm`. (`merge.rs` total
commutativity, set/edge union + Dead-wins join both commutative; merge.rs:15–17.) -/
theorem merge_comm (a b : DocGraph) : merge a b = merge b a := by
  apply DocGraph.ext
  · intro i; simp only [merge_atoms, atomJoin_comm]
  · simp only [merge_order, Finset.union_comm]
  · intro n; simp only [merge_fields, Finset.union_comm]

/-- **`merge_assoc` (ASSOCIATIVITY).** `merge (merge a b) c = merge a (merge b c)`: a finite
colimit is bracket-independent (merge.rs:18–19). -/
theorem merge_assoc (a b c : DocGraph) : merge (merge a b) c = merge a (merge b c) := by
  apply DocGraph.ext
  · intro i; simp only [merge_atoms, atomJoin_assoc]
  · simp only [merge_order, Finset.union_assoc]
  · intro n; simp only [merge_fields, Finset.union_assoc]

/-- **`merge_idem` (IDEMPOTENCE).** `merge a a = a`: re-merging a fork against itself is a no-op
(merge.rs:20). -/
theorem merge_idem (a : DocGraph) : merge a a = a := by
  apply DocGraph.ext
  · intro i; simp only [merge_atoms, atomJoin_idem]
  · simp only [merge_order, Finset.union_idempotent]
  · intro n; simp only [merge_fields, Finset.union_idempotent]

/-- **`merge_total` (TOTALITY).** `merge` is a TOTAL function — every fork has a merge (the union
always exists; the missing order becomes a representable antichain, not a failure; merge.rs:14–15).
This is the catch the graph model fixes: there is no `Option`/error result. -/
theorem merge_total (a b : DocGraph) : ∃ g : DocGraph, g = merge a b := ⟨merge a b, rfl⟩

/-- **`merge_status_dead_wins` (THE STATUS-JOIN, exercised).** If `a` (or `b`) has tombstoned atom
`i` (`a.atoms i = some .dead`), the merged atom is DEAD — regardless of the other side. THIS is the
proof the old `Finset Atom` model could not even STATE: it would have produced a two-element set
{alive, dead} at `i`. Here the keyed map + pointwise `Status.join` gives a SINGLE dead status,
exactly `graph.rs::union_in_place`'s `a.status = a.status.join(other.status)` (graph.rs:277). -/
theorem merge_status_dead_wins (a b : DocGraph) (i : AtomId)
    (h : a.atoms i = some .dead ∨ b.atoms i = some .dead)
    (hpresent : a.atoms i ≠ none ∧ b.atoms i ≠ none) :
    (merge a b).atoms i = some .dead := by
  obtain ⟨hap, hbp⟩ := hpresent
  rw [merge_atoms]
  cases hai : a.atoms i with
  | none => exact absurd hai hap
  | some av =>
    cases hbi : b.atoms i with
    | none => exact absurd hbi hbp
    | some bv =>
      rw [hai, hbi] at h
      simp only [atomJoin]
      rcases h with h | h
      · rw [Option.some.injEq] at h; subst h; simp only [Status.join_dead_left]
      · rw [Option.some.injEq] at h; subst h; simp only [Status.join_dead_right]

/-! ## 4. THE INCLUSION ORDER `⊑` and the UNIVERSAL PROPERTY — merge is the LEAST UPPER BOUND.

Honest framing (audit gap #3): this is NOT "the categorical pushout up to unique iso". It is the
LATTICE JOIN — the LEAST UPPER BOUND in the document inclusion order `⊑` — which in the Pijul graph
model is the colimit-by-union the pushout computes. We prove exactly that: `merge a b` includes both
legs (the cocone) and is below any common upper bound (leastness). §9 PROMOTES this to the
categorical pushout statement in the THIN inclusion category (`merge` IS the pushout of a span, unique
up to iso = equality). The remaining residual — the FULL LABELLED patch category `P` whose morphisms
are patches (not inclusions), and its functoriality — is NAMED, not claimed. -/

/-- **`Includes g h` (`g ⊑ h`).** Document inclusion: `h` advances past `g`. Pointwise on atoms
(`h`'s atom at each present id of `g` is `≥` in the `alive ≤ dead` order), the order-edges contain
`g`'s, and each field's value-set contains `g`'s. This is the order in which `merge` is the JOIN. -/
def Includes (g h : DocGraph) : Prop :=
  (∀ i v, g.atoms i = some v → ∃ w, h.atoms i = some w ∧ Status.le v w) ∧
  g.order ⊆ h.order ∧
  (∀ n, g.fields n ⊆ h.fields n)

@[inherit_doc] infix:50 " ⊑ " => Includes

theorem Includes.refl (g : DocGraph) : g ⊑ g :=
  ⟨fun _ v hv => ⟨v, hv, Status.le_refl v⟩, Finset.Subset.refl _, fun _ => Finset.Subset.refl _⟩

theorem Includes.trans {a b c : DocGraph} (hab : a ⊑ b) (hbc : b ⊑ c) : a ⊑ c := by
  obtain ⟨ha, hao, haf⟩ := hab
  obtain ⟨hb, hbo, hbf⟩ := hbc
  refine ⟨?_, hao.trans hbo, fun n => (haf n).trans (hbf n)⟩
  intro i v hv
  obtain ⟨w, hw, hvw⟩ := ha i v hv
  obtain ⟨u, hu, hwu⟩ := hb i w hw
  exact ⟨u, hu, Status.le_trans hvw hwu⟩

/-- **`merge_includes_left` (a cocone leg).** `a ⊑ merge a b`: the left fork is included in the
merge. On atoms it is `Status.le_join_left` (a present atom advances to the join, never lost);
on order/fields it is `Finset.subset_union_left`. -/
theorem merge_includes_left (a b : DocGraph) : a ⊑ merge a b := by
  refine ⟨?_, ?_, ?_⟩
  · intro i v hv
    rw [merge_atoms]
    cases hbi : b.atoms i with
    | none => rw [hv]; exact ⟨v, rfl, Status.le_refl v⟩
    | some bv => rw [hv]; exact ⟨Status.join v bv, rfl, Status.le_join_left v bv⟩
  · rw [merge_order]; exact Finset.subset_union_left
  · intro n; rw [merge_fields]; exact Finset.subset_union_left

/-- **`merge_includes_right` (the other cocone leg).** `b ⊑ merge a b`. -/
theorem merge_includes_right (a b : DocGraph) : b ⊑ merge a b := by
  refine ⟨?_, ?_, ?_⟩
  · intro i v hv
    rw [merge_atoms]
    cases hai : a.atoms i with
    | none => rw [hv]; exact ⟨v, rfl, Status.le_refl v⟩
    | some av => rw [hv]; exact ⟨Status.join av v, rfl, Status.le_join_right av v⟩
  · rw [merge_order]; exact Finset.subset_union_right
  · intro n; rw [merge_fields]; exact Finset.subset_union_right

/-- **`merge_least` (LEASTNESS).** Any common upper bound `u` (with `a ⊑ u` and `b ⊑ u`) dominates
the merge: `merge a b ⊑ u`. On atoms it is `Status.join_le` (the join is the LUB of the two
statuses); on order/fields it is `Finset.union_subset`. This is what makes `merge` the LEAST upper
bound, not merely AN upper bound. -/
theorem merge_least {a b u : DocGraph} (ha : a ⊑ u) (hb : b ⊑ u) : merge a b ⊑ u := by
  obtain ⟨haa, hao, haf⟩ := ha
  obtain ⟨hba, hbo, hbf⟩ := hb
  refine ⟨?_, ?_, ?_⟩
  · intro i v hv
    rw [merge_atoms] at hv
    cases hai : a.atoms i with
    | none =>
      cases hbi : b.atoms i with
      | none => rw [hai, hbi] at hv; simp only [atomJoin] at hv; exact absurd hv (by simp)
      | some bv =>
        rw [hai, hbi] at hv; simp only [atomJoin, Option.some.injEq] at hv
        subst hv; exact hba i bv hbi
    | some av =>
      cases hbi : b.atoms i with
      | none =>
        rw [hai, hbi] at hv; simp only [atomJoin, Option.some.injEq] at hv
        subst hv; exact haa i av hai
      | some bv =>
        rw [hai, hbi] at hv; simp only [atomJoin, Option.some.injEq] at hv
        subst hv
        obtain ⟨w, hw, haw⟩ := haa i av hai
        obtain ⟨w', hw', hbw'⟩ := hba i bv hbi
        rw [hw] at hw'; rw [Option.some.injEq] at hw'; subst hw'
        exact ⟨w, hw, Status.join_le haw hbw'⟩
  · rw [merge_order]; exact Finset.union_subset hao hbo
  · intro n; rw [merge_fields]; exact Finset.union_subset (haf n) (hbf n)

/-- **`merge_is_lub` (THE UNIVERSAL PROPERTY, as a LATTICE JOIN — honestly).** `merge a b` is the
LEAST UPPER BOUND of `a` and `b` in `⊑`: it includes both legs AND lies below every common upper
bound. This is the join, the colimit-by-union the pushout computes in the Pijul model — stated as
exactly the LUB, no more. §9 promotes it to the categorical pushout in the thin inclusion category
(unique up to iso = equality). RESIDUAL (NAMED, not proved here): the FULL LABELLED patch category
`P` whose morphisms are patches (not inclusions), and its functoriality. -/
theorem merge_is_lub (a b : DocGraph) :
    a ⊑ merge a b ∧ b ⊑ merge a b ∧
    (∀ u, a ⊑ u → b ⊑ u → merge a b ⊑ u) :=
  ⟨merge_includes_left a b, merge_includes_right a b, fun _ ha hb => merge_least ha hb⟩

/-! ## 5. CONFLICT-AS-STATE — TRANSITIVE reachability (audit gap #2), not a one-hop shadow.

`content.rs::reachable` (content.rs:340) is reflexive on `start == target` then a graph walk over
`successors` — i.e. the REFLEXIVE-TRANSITIVE closure of the edge relation. We model exactly that with
`Relation.ReflTransGen`, and a `ConflictAt` as the MUTUAL non-reachability `content.rs::walk` tests
(content.rs:251–254): two distinct live successors of a shared `p`, neither reaching the other. -/

/-- **`Reaches g a b`** — `b` is reachable from `a` by following order-edges through any atoms
(`content.rs::reachable`, content.rs:340): the reflexive-transitive closure of the edge relation
`fun x y => (x, y) ∈ g.order`. Reflexive (the Rust `if start == target { return true }`), transitive
(the stack walk over `successors`). NOT a one-hop edge test — this is the audited fix. -/
def Reaches (g : DocGraph) (a b : AtomId) : Prop :=
  Relation.ReflTransGen (fun x y => (x, y) ∈ g.order) a b

theorem Reaches.refl (g : DocGraph) (a : AtomId) : Reaches g a a := Relation.ReflTransGen.refl

theorem Reaches.single {g : DocGraph} {a b : AtomId} (h : (a, b) ∈ g.order) : Reaches g a b :=
  Relation.ReflTransGen.single h

theorem Reaches.trans {g : DocGraph} {a b c : AtomId}
    (hab : Reaches g a b) (hbc : Reaches g b c) : Reaches g a c :=
  Relation.ReflTransGen.trans hab hbc

/-- A one-hop edge through a chain DOES reach transitively: `a→b→c` (two edges) gives `Reaches a c`.
This is the property a one-hop model MISSES. -/
theorem Reaches.of_two {g : DocGraph} {a b c : AtomId}
    (hab : (a, b) ∈ g.order) (hbc : (b, c) ∈ g.order) : Reaches g a c :=
  (Reaches.single hab).trans (Reaches.single hbc)

/-- **`ConflictAt g p x y`** — a transitive PROSE antichain (`content.rs::walk`, content.rs:251):
`x` and `y` are DISTINCT, both LIVE, both reached from a shared predecessor `p`, and MUTUALLY
non-reachable (`¬ Reaches g x y ∧ ¬ Reaches g y x`). Mutual non-reachability is the transitive form
of "no edge between them" the Rust antichain filter computes — a genuine concurrent fork with no
linear order, surfaced as a first-class conflict STATE (not a merge failure). -/
def ConflictAt (g : DocGraph) (p x y : AtomId) : Prop :=
  x ≠ y ∧
  g.atoms x = some .alive ∧ g.atoms y = some .alive ∧
  Reaches g p x ∧ Reaches g p y ∧
  ¬ Reaches g x y ∧ ¬ Reaches g y x

/-! ### A concrete two-fork conflict that is a WELL-FORMED merged `DocGraph` (not a failure). -/

/-- Atom ids for the witness: a shared base `p`, and two concurrent forks `1`, `2`. -/
def pId : AtomId := 10
def aId : AtomId := 1
def bId : AtomId := 2

/-- The base graph: atoms `p`, `1`, `2` all ALIVE, NO order edges yet. (`DocGraph::new` + three
inserts.) -/
def base : DocGraph where
  atoms := fun i => if i = pId ∨ i = aId ∨ i = bId then some .alive else none
  order := ∅
  fields := fun _ => ∅

/-- Fork A: edge `p → 1` (`Connect p 1`). -/
def forkA : DocGraph where
  atoms := fun _ => none
  order := {(pId, aId)}
  fields := fun _ => ∅

/-- Fork B: edge `p → 2` (`Connect p 2`). -/
def forkB : DocGraph where
  atoms := fun _ => none
  order := {(pId, bId)}
  fields := fun _ => ∅

/-- The merged conflict graph: `merge (merge base forkA) forkB` — `p,1,2` alive, edges `p→1`, `p→2`,
NO edge `1↔2`. A WELL-FORMED `DocGraph`, the union of two additive forks. -/
def conflictGraph : DocGraph := merge (merge base forkA) forkB

@[simp] theorem conflictGraph_atom_p : conflictGraph.atoms pId = some .alive := by decide
@[simp] theorem conflictGraph_atom_a : conflictGraph.atoms aId = some .alive := by decide
@[simp] theorem conflictGraph_atom_b : conflictGraph.atoms bId = some .alive := by decide
@[simp] theorem conflictGraph_order :
    conflictGraph.order = ({(pId, aId), (pId, bId)} : Finset (AtomId × AtomId)) := by decide

/-- The edges `p→1` and `p→2` are present in the conflict graph; the cross edges `1→2` and `2→1`
are ABSENT — this is what makes `1` and `2` a genuine transitive antichain. -/
theorem conflictGraph_edges :
    (pId, aId) ∈ conflictGraph.order ∧ (pId, bId) ∈ conflictGraph.order ∧
    (aId, bId) ∉ conflictGraph.order ∧ (bId, aId) ∉ conflictGraph.order := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- In a graph whose ONLY edges leave `pId` (none leave `aId`/`bId`), `Reaches g aId bId` forces
`aId = bId`: the RTC from `aId` can take no step (no outgoing edge), so it is reflexivity only. -/
theorem reaches_stuck_of_no_out {g : DocGraph} {x y : AtomId}
    (hx : ∀ z, (x, z) ∉ g.order) (h : Reaches g x y) : x = y := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    -- ih : x = (the intermediate node); the step leaves that node, but it equals x, contradiction.
    subst ih; exact absurd hstep (hx _)

/-- **`merge_has_conflict` (CONFLICT-AS-STATE, transitive).** The merged `conflictGraph` carries a
genuine `ConflictAt pId aId bId`: `1` and `2` are distinct, both alive, both reached from `p`, and
MUTUALLY non-`Reaches`able (a transitive antichain — neither reaches the other through ANY path,
because neither has an outgoing edge). The conflict is a WELL-FORMED merged state, not a failure. -/
theorem merge_has_conflict : ConflictAt conflictGraph pId aId bId := by
  have hao : ∀ z, (aId, z) ∉ conflictGraph.order := by
    intro z hmem; rw [conflictGraph_order] at hmem
    simp only [aId, pId, bId, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq,
      Nat.reduceEqDiff, false_and, or_self] at hmem
  have hbo : ∀ z, (bId, z) ∉ conflictGraph.order := by
    intro z hmem; rw [conflictGraph_order] at hmem
    simp only [bId, pId, aId, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq,
      Nat.reduceEqDiff, false_and, or_self] at hmem
  refine ⟨by decide, conflictGraph_atom_a, conflictGraph_atom_b, ?_, ?_, ?_, ?_⟩
  · exact Reaches.single (by rw [conflictGraph_order]; decide)
  · exact Reaches.single (by rw [conflictGraph_order]; decide)
  · intro h; exact absurd (reaches_stuck_of_no_out hao h) (by decide)
  · intro h; exact absurd (reaches_stuck_of_no_out hbo h) (by decide)

/-! ### Resolution — an additive `Connect` collapses the antichain (and is additive, `g ⊑ resolved`). -/

/-- The resolution patch: add edge `1 → 2` (`Connect 1 2`). An ordinary ADDITIVE Connect. -/
def resolvePatch : DocGraph where
  atoms := fun _ => none
  order := {(aId, bId)}
  fields := fun _ => ∅

/-- The resolved graph: `merge conflictGraph resolvePatch` — now `1 → 2`. -/
def resolved : DocGraph := merge conflictGraph resolvePatch

@[simp] theorem resolved_has_cross_edge : (aId, bId) ∈ resolved.order := by
  rw [show resolved = merge conflictGraph resolvePatch from rfl, merge_order]
  exact Finset.mem_union_right _ (by decide)

/-- **`resolve_collapses` (RESOLUTION).** Adding the edge `1 → 2` makes `Reaches resolved aId bId`
HOLD — so `1` and `2` are no longer mutually non-reachable, the antichain is gone, and `ConflictAt`
fails. AND the resolution is ADDITIVE: `conflictGraph ⊑ resolved` (a `Connect` only grows the graph).
So the conflict is resolved by an ordinary monotone patch, never a destructive rewrite. -/
theorem resolve_collapses :
    Reaches resolved aId bId ∧ ¬ ConflictAt resolved pId aId bId ∧ conflictGraph ⊑ resolved := by
  have hreach : Reaches resolved aId bId := Reaches.single resolved_has_cross_edge
  refine ⟨hreach, ?_, ?_⟩
  · rintro ⟨_, _, _, _, _, hnab, _⟩; exact hnab hreach
  · exact merge_includes_left conflictGraph resolvePatch

/-! ## 6. THE TWO-REGIME SPLIT (§2.4) — `prose_iconfluent` vs `field_not_iconfluent`.

`regime.rs` draws the line: the prose/liveness fragment is grow-only and ALWAYS glues by union
(I-confluent); a single-valued field is NOT grow-only and a concurrent clash is a REAL conflict.
We connect both to the shape of `Confluence.IConfluent` (`∀ x y, I x → I y → I (x ⊔ y)`). -/

/-- **`prose_iconfluent` (the I-confluent side).** A grow-only LIVENESS invariant survives merge: if
`I` is monotone in the sense that a present atom's advancing status preserves it, AND `I` holds of
both legs, it holds of the merge. We state the canonical grow-only liveness invariant — "the set of
PRESENT atom-ids only grows" — as the I-confluent property: present-in-`a` and present-in-`b` both
imply present-in-`merge a b`. This is the `Confluence.IConfluent` shape (`I a → I b → I (merge a b)`)
for the prose fragment, the always-glues case (`regime.rs::Regime::Prose`). -/
theorem prose_iconfluent (a b : DocGraph) (i : AtomId)
    (h : a.atoms i ≠ none ∨ b.atoms i ≠ none) :
    (merge a b).atoms i ≠ none := by
  rw [merge_atoms]
  cases hai : a.atoms i with
  | none =>
    cases hbi : b.atoms i with
    | none => rw [hai, hbi] at h; simp at h
    | some bv => simp [atomJoin]
  | some av =>
    cases hbi : b.atoms i with
    | none => simp [atomJoin]
    | some bv => simp [atomJoin]

/-- **`field_not_iconfluent` (the non-monotone boundary).** The single-valued field store is NOT
I-confluent: two graphs each single-valued at name `n` (one value apiece) merge to TWO values at
`n` — a real clash. We CONSTRUCT the clashing pair: `gx` assigns `{0}` to `n`, `gy` assigns `{1}`,
each is single-valued (`card = 1`), but `(merge gx gy).fields n = {0, 1}` has `card = 2`. This is
the `regime.rs::Regime::Field` conflict — the consensus-needing boundary the §2.4 split draws. -/
theorem field_not_iconfluent :
    ∃ (gx gy : DocGraph) (n : Name),
      (gx.fields n).card = 1 ∧ (gy.fields n).card = 1 ∧
      (merge gx gy).fields n = ({0, 1} : Finset Val) ∧
      2 ≤ ((merge gx gy).fields n).card := by
  refine ⟨⟨fun _ => none, ∅, fun _ => {0}⟩, ⟨fun _ => none, ∅, fun _ => {1}⟩, 0, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · rw [merge_fields]; decide
  · rw [merge_fields]; decide

/-! ## 7. NON-VACUITY teeth — the concrete forks, the dead-wins join, the conflict/resolution edges.

`#guard`s are the project's machine-checked non-vacuity teeth (a false `#guard` is a BUILD ERROR).
`DocGraph` has function fields (no `DecidableEq`), so we guard on its `.order` / `.atoms i` /
`.fields n` PROJECTIONS, which are decidable. The model⟺Rust differential on a concrete trace. -/

-- The concrete forks merge to the conflict graph's expected atoms + edges.
#guard conflictGraph.atoms pId == some Status.alive
#guard conflictGraph.atoms aId == some Status.alive
#guard conflictGraph.atoms bId == some Status.alive
#guard conflictGraph.order == ({(pId, aId), (pId, bId)} : Finset (AtomId × AtomId))
-- The CROSS edges are ABSENT (the transitive antichain): 1↛2 and 2↛1 directly.
#guard decide ((aId, bId) ∉ conflictGraph.order)
#guard decide ((bId, aId) ∉ conflictGraph.order)
-- THE DEAD-WINS JOIN on a concrete pair: alive ⊔ dead = dead (the status-join exercised).
#guard atomJoin (some Status.alive) (some Status.dead) == some Status.dead
#guard atomJoin (some Status.dead) (some Status.alive) == some Status.dead
#guard atomJoin (some Status.alive) (some Status.alive) == some Status.alive
-- RESOLUTION adds the cross edge 1→2 (the antichain collapses).
#guard decide ((aId, bId) ∈ resolved.order)
-- THE FIELD CLASH: two single-valued graphs merge to a 2-element value set.
#guard (merge (⟨fun _ => none, ∅, fun _ => {0}⟩ : DocGraph)
              (⟨fun _ => none, ∅, fun _ => {1}⟩ : DocGraph)).fields 0
       == ({0, 1} : Finset Val)

/-! ## 8. Axiom hygiene — every keystone is kernel-clean (⊆ {propext, Classical.choice, Quot.sound}). -/

#assert_axioms atomJoin_comm
#assert_axioms atomJoin_assoc
#assert_axioms atomJoin_idem
#assert_axioms merge_comm
#assert_axioms merge_assoc
#assert_axioms merge_idem
#assert_axioms merge_total
#assert_axioms merge_status_dead_wins
#assert_axioms Includes.refl
#assert_axioms Includes.trans
#assert_axioms merge_includes_left
#assert_axioms merge_includes_right
#assert_axioms merge_least
#assert_axioms merge_is_lub
#assert_axioms merge_has_conflict
#assert_axioms resolve_collapses
#assert_axioms prose_iconfluent
#assert_axioms field_not_iconfluent

/-! ## 9. THE CATEGORICAL PUSHOUT — `merge` is the pushout in the THIN inclusion category,
unique up to iso (= equality).

This CLOSES the categorical residual §4 named — for the HONEST, tractable model. The document states
ordered by inclusion `⊑` form a THIN (preorder) category: `Includes.refl`/`Includes.trans` are the
identity/composition, and between any two objects there is AT MOST ONE morphism. In a thin category
a colimit is a least upper bound, and conversely the join `merge a b` IS the pushout of any span
`a ⊑← c →⊑ b`. "Unique up to unique iso" degenerates here to "unique up to EQUALITY": the only isos
in a poset are identities, because `⊑` is ANTISYMMETRIC (`Includes.antisymm` below) — `g ⊑ h` and
`h ⊑ g` force `g = h`. This is a correct, standard categorical fact; what it does NOT do is build the
FULL LABELLED patch category `P` (morphisms = patches, not inclusions), a larger non-thin category —
that remains the named residual. -/

/-- **`Status.le_antisymm`.** The monotone status order `alive ≤ dead` is ANTISYMMETRIC: `a ≤ b` and
`b ≤ a` force `a = b`. (Cases on `a`, `b`; the `dead ≤ alive = False` clause kills the cross cases.) -/
theorem Status.le_antisymm {a b : Status} (hab : Status.le a b) (hba : Status.le b a) : a = b := by
  cases a <;> cases b <;> first | rfl | (simp only [Status.le] at hab hba)

/-- **`Includes.antisymm`.** Document inclusion `⊑` is ANTISYMMETRIC: `g ⊑ h` and `h ⊑ g` force
`g = h`. With `Includes.refl`/`Includes.trans` this makes `⊑` a PARTIAL ORDER (a poset), so the thin
category over it has only identity isomorphisms. On atoms each present id is forced equal by
`Status.le_antisymm` (the some/none cross cases are impossible — the `⊑` atom clause yields a `some`
on the other side); on order/fields it is `Finset.Subset.antisymm`. -/
theorem Includes.antisymm {g h : DocGraph} (hgh : g ⊑ h) (hhg : h ⊑ g) : g = h := by
  obtain ⟨hga, hgo, hgf⟩ := hgh
  obtain ⟨hha, hho, hhf⟩ := hhg
  apply DocGraph.ext
  · intro i
    cases hgi : g.atoms i with
    | none =>
      cases hhi : h.atoms i with
      | none => rfl
      | some w =>
        obtain ⟨v, hv, _⟩ := hha i w hhi
        rw [hgi] at hv; simp at hv
    | some v =>
      cases hhi : h.atoms i with
      | none =>
        obtain ⟨w, hw, _⟩ := hga i v hgi
        rw [hhi] at hw; simp at hw
      | some w =>
        obtain ⟨w2, hw2, hvw⟩ := hga i v hgi
        rw [hhi, Option.some.injEq] at hw2; subst hw2
        obtain ⟨v2, hv2, hwv⟩ := hha i w hhi
        rw [hgi, Option.some.injEq] at hv2; subst hv2
        rw [Status.le_antisymm hvw hwv]
  · exact Finset.Subset.antisymm hgo hho
  · intro n; exact Finset.Subset.antisymm (hgf n) (hhf n)

/-- **`Includes.le_antisymm`** — the poset law, stated alongside the existing `refl`/`trans`: `⊑` is
a PARTIAL ORDER. (Alias of `Includes.antisymm`, named to read as the order law.) -/
theorem Includes.le_antisymm {g h : DocGraph} (hgh : g ⊑ h) (hhg : h ⊑ g) : g = h :=
  Includes.antisymm hgh hhg

/-- **`IsCocone a b d`** — `d` is a cocone over the two feet `a`, `b`: both include into `d`
(`a ⊑ d ∧ b ⊑ d`). In the THIN category over a span with apex `c` (`c ⊑ a`, `c ⊑ b`) the square
COMMUTES AUTOMATICALLY — `c ⊑ d` via either leg is the same morphism because between `c` and `d`
there is at most one arrow — so the cocone condition reduces to "`d` is an upper bound of the two
feet". -/
def IsCocone (a b d : DocGraph) : Prop := a ⊑ d ∧ b ⊑ d

/-- **`IsPushout c a b d`** — `d` is the pushout of the span `a ⊑← c →⊑ b` in the thin inclusion
category: `c` includes into both feet, `d` is a cocone over the feet, and `d` is the LEAST such
cocone (universality). In a poset this is exactly the join of the feet — independent of the apex
`c`, which contributes no extra constraint to the colimit object. -/
def IsPushout (c a b d : DocGraph) : Prop :=
  c ⊑ a ∧ c ⊑ b ∧ IsCocone a b d ∧ ∀ d', IsCocone a b d' → d ⊑ d'

/-- **`merge_isPushout` (merge IS the pushout).** For any span `a ⊑← c →⊑ b`, the join `merge a b`
is its pushout in the thin inclusion category. The cocone legs are `merge_includes_left/right`;
universality is `merge_least`. The apex `c` plays NO role in the colimit object — the poset pushout is
the join of the two FEET, independent of `c` (the span's apex only certifies that `a`, `b` share a
common past). -/
theorem merge_isPushout (c a b : DocGraph) (hca : c ⊑ a) (hcb : c ⊑ b) :
    IsPushout c a b (merge a b) := by
  refine ⟨hca, hcb, ⟨merge_includes_left a b, merge_includes_right a b⟩, ?_⟩
  intro d' hd'
  exact merge_least hd'.1 hd'.2

/-- **`pushout_unique` (UNIQUE UP TO ISO = EQUALITY).** Any two pushouts of the same span are EQUAL.
From universality each is below the other (`d ⊑ d'` because `d` is the least cocone and `d'` is a
cocone; symmetrically `d' ⊑ d`), then `Includes.antisymm`. In a general category the pushout is
unique up to unique iso; in this THIN category the only isos are identities (antisymmetry), so
"unique up to iso" IS "unique up to equality". -/
theorem pushout_unique {c a b d d' : DocGraph}
    (hd : IsPushout c a b d) (hd' : IsPushout c a b d') : d = d' := by
  obtain ⟨_, _, hcone, huniv⟩ := hd
  obtain ⟨_, _, hcone', huniv'⟩ := hd'
  exact Includes.antisymm (huniv d' hcone') (huniv' d hcone)

/-- **`pushout_iff_merge`.** A graph `d` is the pushout of the span `a ⊑← c →⊑ b` IFF it equals
`merge a b`. Combines `merge_isPushout` (existence) and `pushout_unique` (uniqueness). -/
theorem pushout_iff_merge {c a b d : DocGraph} (hca : c ⊑ a) (hcb : c ⊑ b) :
    IsPushout c a b d ↔ d = merge a b := by
  constructor
  · intro hd; exact pushout_unique hd (merge_isPushout c a b hca hcb)
  · intro h; subst h; exact merge_isPushout c a b hca hcb

/-! ### A concrete inhabited pushout (non-vacuity tooth). -/

/-- **`conflictGraph_isPushout` (NON-VACUITY).** A concrete inhabited pushout: in the span with apex
`base` and feet `merge base forkA`, `merge base forkB`, the pushout object is `conflictGraph`. Note
`conflictGraph = merge (merge base forkA) forkB`, and by comm/assoc/idem of `merge` this is the join
of the two FEET — proved here by `Includes.antisymm` against `merge` of the feet, then `merge_isPushout`.
This exhibits that `IsPushout` is genuinely inhabited (true and non-trivially so). -/
theorem conflictGraph_isPushout :
    IsPushout base (merge base forkA) (merge base forkB) conflictGraph := by
  have heq : conflictGraph = merge (merge base forkA) (merge base forkB) := by
    apply Includes.antisymm
    · -- conflictGraph = merge (merge base forkA) forkB ⊑ merge (merge base forkA) (merge base forkB)
      show merge (merge base forkA) forkB ⊑ merge (merge base forkA) (merge base forkB)
      apply merge_least
      · exact merge_includes_left _ _
      · exact Includes.trans (merge_includes_right base forkB) (merge_includes_right _ _)
    · -- merge (merge base forkA) (merge base forkB) ⊑ conflictGraph
      show merge (merge base forkA) (merge base forkB) ⊑ merge (merge base forkA) forkB
      apply merge_least
      · exact merge_includes_left _ _
      · apply merge_least
        · exact Includes.trans (merge_includes_left base forkA) (merge_includes_left _ _)
        · exact merge_includes_right _ _
  rw [heq]
  exact merge_isPushout base (merge base forkA) (merge base forkB)
    (merge_includes_left base forkA) (merge_includes_left base forkB)

/-! ## 9a. Axiom hygiene for the categorical-pushout keystones. -/

#assert_axioms Status.le_antisymm
#assert_axioms Includes.antisymm
#assert_axioms Includes.le_antisymm
#assert_axioms merge_isPushout
#assert_axioms pushout_unique
#assert_axioms pushout_iff_merge
#assert_axioms conflictGraph_isPushout

end Dregg2.Deos.DocMerge

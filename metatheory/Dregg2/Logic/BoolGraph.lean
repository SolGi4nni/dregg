/-
# Dregg2.Logic.BoolGraph -- an exact Boolean constraint graph over any field

This module is a small, self-contained ground target for later `Pred` and HOL
lowerings. It deliberately does not use the unsound convention "truth is zero,
AND is field addition". Every Boolean wire is constrained to `{0,1}`, and
**one means true** throughout.

An atomic proposition is a zero test on a field residual. `ZeroGate` uses an
inverse witness instead of exponentiation:

    b(b-1) = 0,       x b = 0,       x z = 1-b.

Thus `b = 1` exactly when `x = 0`. The Boolean gates are quadratic, the fold
graphs are chains of quadratic gates, and `Graph` is the exact relational
compiler for a small reified propositional language. All results are generic
over `Field F`; no field-size or characteristic assumption is hidden.
-/

import Mathlib.Algebra.Field.Basic
import Dregg2.Tactics

namespace Dregg2.Logic.BoolGraph

variable {F : Type*} [Field F]

/-! ## Boolean wires and primitive gates -/

/-- A field wire is Boolean precisely when it satisfies the standard quadratic
constraint. -/
def IsBit (b : F) : Prop := b * (b - 1) = 0

theorem isBit_iff (b : F) : IsBit b ↔ b = 0 ∨ b = 1 := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  · rintro (rfl | rfl) <;> simp [IsBit]

theorem bit_zero_or_one {b : F} (hb : IsBit b) : b = 0 ∨ b = 1 :=
  (isBit_iff b).mp hb

theorem bit_zero_iff_not_one {b : F} (hb : IsBit b) : b = 0 ↔ b ≠ 1 := by
  rcases bit_zero_or_one hb with rfl | rfl <;> simp

/-- Quadratic one-means-true conjunction gate. -/
def AndGate (a b out : F) : Prop :=
  IsBit a ∧ IsBit b ∧ IsBit out ∧ out = a * b

/-- Quadratic one-means-true disjunction gate. -/
def OrGate (a b out : F) : Prop :=
  IsBit a ∧ IsBit b ∧ IsBit out ∧ out = a + b - a * b

/-- Linear one-means-true negation gate, with Booleanity made explicit. -/
def NotGate (a out : F) : Prop :=
  IsBit a ∧ IsBit out ∧ out = 1 - a

theorem andGate_complete {a b : F} (ha : IsBit a) (hb : IsBit b) :
    AndGate a b (a * b) := by
  rcases bit_zero_or_one ha with rfl | rfl <;>
    rcases bit_zero_or_one hb with rfl | rfl <;> simp [AndGate, IsBit]

theorem orGate_complete {a b : F} (ha : IsBit a) (hb : IsBit b) :
    OrGate a b (a + b - a * b) := by
  rcases bit_zero_or_one ha with rfl | rfl <;>
    rcases bit_zero_or_one hb with rfl | rfl <;> simp [OrGate, IsBit]

theorem notGate_complete {a : F} (ha : IsBit a) : NotGate a (1 - a) := by
  rcases bit_zero_or_one ha with rfl | rfl <;> simp [NotGate, IsBit]

theorem andGate_one_iff {a b out : F} (h : AndGate a b out) :
    out = 1 ↔ a = 1 ∧ b = 1 := by
  rcases h with ⟨ha, hb, _, rfl⟩
  rcases bit_zero_or_one ha with rfl | rfl <;>
    rcases bit_zero_or_one hb with rfl | rfl <;> simp

theorem orGate_one_iff {a b out : F} (h : OrGate a b out) :
    out = 1 ↔ a = 1 ∨ b = 1 := by
  rcases h with ⟨ha, hb, _, rfl⟩
  rcases bit_zero_or_one ha with rfl | rfl <;>
    rcases bit_zero_or_one hb with rfl | rfl <;> simp

theorem notGate_one_iff {a out : F} (h : NotGate a out) :
    out = 1 ↔ a = 0 := by
  rcases h with ⟨ha, _, rfl⟩
  rcases bit_zero_or_one ha with rfl | rfl <;> simp

/-! ## Exact inverse-witness zero testing -/

/-- `b` is the one-means-zero bit for residual `x`; `inv` is an inverse witness
used only in the nonzero branch. These are all low-degree field equations. -/
def ZeroGate (x b inv : F) : Prop :=
  IsBit b ∧ x * b = 0 ∧ x * inv = 1 - b

/-- Soundness is exact, not probabilistic: every satisfying witness reports the
right zero bit. -/
theorem zeroGate_sound {x b inv : F} (h : ZeroGate x b inv) :
    b = 1 ↔ x = 0 := by
  rcases h with ⟨_, hxb, hxi⟩
  constructor
  · intro hb
    simpa [hb] using hxb
  · intro hx
    subst x
    have hzero : (1 : F) - b = 0 := by simpa using hxi.symm
    have h1b : (1 : F) = b := sub_eq_zero.mp hzero
    exact h1b.symm

/-- Total completeness supplies the inverse witness in the nonzero branch. -/
theorem zeroGate_complete (x : F) :
    ∃ b inv, ZeroGate x b inv ∧ (b = 1 ↔ x = 0) := by
  by_cases hx : x = 0
  · refine ⟨1, 0, ?_, ?_⟩
    · simp [ZeroGate, IsBit, hx]
    · simp [hx]
  · refine ⟨0, x⁻¹, ?_, ?_⟩
    · simp [ZeroGate, IsBit, hx]
    · simp [hx]

/-! ## N-ary Boolean folds as quadratic gate chains -/

/-- A low-degree conjunction chain. `nil` returns true; every `cons` adds one
quadratic gate rather than increasing the degree of a single constraint. -/
inductive AndFoldGraph : List F → F → Prop
  | nil : AndFoldGraph [] 1
  | cons {x : F} {xs : List F} {tail out : F} :
      AndFoldGraph xs tail → AndGate x tail out → AndFoldGraph (x :: xs) out

/-- A low-degree disjunction chain. `nil` returns false. -/
inductive OrFoldGraph : List F → F → Prop
  | nil : OrFoldGraph [] 0
  | cons {x : F} {xs : List F} {tail out : F} :
      OrFoldGraph xs tail → OrGate x tail out → OrFoldGraph (x :: xs) out

def AllTrue (xs : List F) : Prop := ∀ x ∈ xs, x = 1
def AnyTrue (xs : List F) : Prop := ∃ x ∈ xs, x = 1

theorem andFoldGraph_sound {xs : List F} {out : F} (h : AndFoldGraph xs out) :
    IsBit out ∧ (out = 1 ↔ AllTrue xs) := by
  induction h with
  | nil =>
      simp [IsBit, AllTrue]
  | @cons x xs tail out hfold hgate ih =>
      refine ⟨hgate.2.2.1, ?_⟩
      rw [andGate_one_iff hgate, ih.2]
      simp only [AllTrue, List.forall_mem_cons]

theorem orFoldGraph_sound {xs : List F} {out : F} (h : OrFoldGraph xs out) :
    IsBit out ∧ (out = 1 ↔ AnyTrue xs) := by
  induction h with
  | nil =>
      simp [IsBit, AnyTrue]
  | @cons x xs tail out hfold hgate ih =>
      refine ⟨hgate.2.2.1, ?_⟩
      rw [orGate_one_iff hgate, ih.2]
      constructor
      · rintro (hx | ⟨y, hy, hy1⟩)
        · exact ⟨x, by simp, hx⟩
        · exact ⟨y, List.mem_cons_of_mem x hy, hy1⟩
      · rintro ⟨y, hy, hy1⟩
        rcases List.mem_cons.mp hy with rfl | hy
        · exact Or.inl hy1
        · exact Or.inr ⟨y, hy, hy1⟩

theorem andFoldGraph_complete (xs : List F) (hbits : ∀ x ∈ xs, IsBit x) :
    ∃ out, AndFoldGraph xs out := by
  induction xs with
  | nil => exact ⟨1, .nil⟩
  | cons x xs ih =>
      obtain ⟨tail, htail⟩ := ih (by
        intro y hy
        exact hbits y (List.mem_cons_of_mem x hy))
      have hx : IsBit x := hbits x (by simp)
      have htailBit : IsBit tail := (andFoldGraph_sound htail).1
      exact ⟨x * tail, .cons htail (andGate_complete hx htailBit)⟩

theorem orFoldGraph_complete (xs : List F) (hbits : ∀ x ∈ xs, IsBit x) :
    ∃ out, OrFoldGraph xs out := by
  induction xs with
  | nil => exact ⟨0, .nil⟩
  | cons x xs ih =>
      obtain ⟨tail, htail⟩ := ih (by
        intro y hy
        exact hbits y (List.mem_cons_of_mem x hy))
      have hx : IsBit x := hbits x (by simp)
      have htailBit : IsBit tail := (orFoldGraph_sound htail).1
      exact ⟨x + tail - x * tail, .cons htail (orGate_complete hx htailBit)⟩

/-! ## A reified propositional source and exact relational compiler -/

/-- Atoms name field residuals. An atom is true exactly when its residual is
zero; this makes equality atoms `lhs-rhs` a direct specialization. -/
inductive Formula (Atom : Type*) where
  | atom : Atom → Formula Atom
  | top : Formula Atom
  | bot : Formula Atom
  | not : Formula Atom → Formula Atom
  | and : Formula Atom → Formula Atom → Formula Atom
  | or : Formula Atom → Formula Atom → Formula Atom
  deriving Repr

def Eval {Atom : Type*} (residual : Atom → F) : Formula Atom → Prop
  | .atom a => residual a = 0
  | .top => True
  | .bot => False
  | .not p => ¬ Eval residual p
  | .and p q => Eval residual p ∧ Eval residual q
  | .or p q => Eval residual p ∨ Eval residual q

/-- The compiler relation is a graph of primitive field gates. Existential
intermediate wires and inverse witnesses are constructor fields, so this is an
exact mathematical model of the emitted witness/constraint graph. -/
inductive Graph {Atom : Type*} (residual : Atom → F) : Formula Atom → F → Prop
  | atom (a : Atom) {out inv : F} :
      ZeroGate (residual a) out inv → Graph residual (.atom a) out
  | top : Graph residual .top 1
  | bot : Graph residual .bot 0
  | not {p : Formula Atom} {a out : F} :
      Graph residual p a → NotGate a out → Graph residual (.not p) out
  | and {p q : Formula Atom} {a b out : F} :
      Graph residual p a → Graph residual q b → AndGate a b out →
      Graph residual (.and p q) out
  | or {p q : Formula Atom} {a b out : F} :
      Graph residual p a → Graph residual q b → OrGate a b out →
      Graph residual (.or p q) out

/-- Every satisfying compiled graph has a Boolean output and that output is one
exactly when the source formula is true. -/
theorem graph_sound {Atom : Type*} {residual : Atom → F} {p : Formula Atom} {out : F}
    (h : Graph residual p out) : IsBit out ∧ (out = 1 ↔ Eval residual p) := by
  induction h with
  | atom a hzero =>
      exact ⟨hzero.1, zeroGate_sound hzero⟩
  | top =>
      simp [IsBit, Eval]
  | bot =>
      simp [IsBit, Eval]
  | not hgraph hgate ih =>
      refine ⟨hgate.2.1, ?_⟩
      rw [notGate_one_iff hgate, bit_zero_iff_not_one ih.1]
      exact not_congr ih.2
  | and hp hq hgate ihp ihq =>
      refine ⟨hgate.2.2.1, ?_⟩
      rw [andGate_one_iff hgate, ihp.2, ihq.2]
      rfl
  | or hp hq hgate ihp ihq =>
      refine ⟨hgate.2.2.1, ?_⟩
      rw [orGate_one_iff hgate, ihp.2, ihq.2]
      rfl

/-- The graph compiler is total: every source formula has a satisfying witness
assignment. This theorem constructs every intermediate and inverse witness. -/
theorem graph_complete {Atom : Type*} (residual : Atom → F) (p : Formula Atom) :
    ∃ out, Graph residual p out := by
  induction p with
  | atom a =>
      obtain ⟨out, inv, hzero, _⟩ := zeroGate_complete (residual a)
      exact ⟨out, .atom a hzero⟩
  | top => exact ⟨1, .top⟩
  | bot => exact ⟨0, .bot⟩
  | not p ih =>
      obtain ⟨a, ha⟩ := ih
      have abit : IsBit a := (graph_sound ha).1
      exact ⟨1 - a, .not ha (notGate_complete abit)⟩
  | and p q ihp ihq =>
      obtain ⟨a, ha⟩ := ihp
      obtain ⟨b, hb⟩ := ihq
      have abit : IsBit a := (graph_sound ha).1
      have bbit : IsBit b := (graph_sound hb).1
      exact ⟨a * b, .and ha hb (andGate_complete abit bbit)⟩
  | or p q ihp ihq =>
      obtain ⟨a, ha⟩ := ihp
      obtain ⟨b, hb⟩ := ihq
      have abit : IsBit a := (graph_sound ha).1
      have bbit : IsBit b := (graph_sound hb).1
      exact ⟨a + b - a * b, .or ha hb (orGate_complete abit bbit)⟩

/-- Acceptance means that some satisfying graph assignment exposes output one. -/
def Accepts {Atom : Type*} (residual : Atom → F) (p : Formula Atom) : Prop :=
  ∃ out, Graph residual p out ∧ out = 1

theorem compile_sound {Atom : Type*} {residual : Atom → F} {p : Formula Atom}
    (h : Accepts residual p) : Eval residual p := by
  obtain ⟨out, hgraph, hout⟩ := h
  exact (graph_sound hgraph).2.mp hout

theorem compile_complete {Atom : Type*} {residual : Atom → F} {p : Formula Atom}
    (h : Eval residual p) : Accepts residual p := by
  obtain ⟨out, hgraph⟩ := graph_complete residual p
  exact ⟨out, hgraph, (graph_sound hgraph).2.mpr h⟩

/-- The corrected compiler is an exact decision relation over every field. -/
theorem compile_exact {Atom : Type*} (residual : Atom → F) (p : Formula Atom) :
    Accepts residual p ↔ Eval residual p :=
  ⟨compile_sound, compile_complete⟩

#assert_all_clean [
  isBit_iff,
  andGate_one_iff,
  orGate_one_iff,
  notGate_one_iff,
  zeroGate_sound,
  zeroGate_complete,
  andFoldGraph_sound,
  orFoldGraph_sound,
  andFoldGraph_complete,
  orFoldGraph_complete,
  graph_sound,
  graph_complete,
  compile_sound,
  compile_complete,
  compile_exact
]

end Dregg2.Logic.BoolGraph

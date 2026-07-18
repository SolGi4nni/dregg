/-
# Dregg2.Circuit.R1csFr — R1CS over Fr (the BN254 scalar field): the FOUNDATION for the
Lean-authored gnark verifier.

`Dregg2/Circuit.lean` (the v1 rail) modeled an AIR-shaped equality-gate system over ℤ with
degree-UNBOUNDED `Expr` nesting inside a single constraint. That rail is dead for the gnark
target: gnark compiles a frontend op-DAG to **R1CS over a prime field** — every constraint is
the BILINEAR form `⟨A,z⟩ · ⟨B,z⟩ = ⟨C,z⟩` with A/B/C linear combinations, nothing deeper.
This module is that object, genuinely:

  * **Fr** = `ZMod rBN254` — the BN254 scalar field (gnark's `ecc.BN254` `ScalarField`),
    `r = 21888242871839275222246405745257275088548364400416034343698204186575808495617`.
  * **`Wire`** — the gnark-frontend-style op-DAG: witness variables, constants, `add`, `mul`,
    `select` (gnark `api.Select`: `b·(x−y)+y`, the field mux). A **`Circuit`** is a list of
    `assertIsEqual` pairs over wires (gnark `api.AssertIsEqual`).
  * **`Circuit.satisfied`** — the frontend semantics: every asserted pair evaluates equal.
  * **`lowerWire`/`Circuit.lower`** — the compilation to R1CS: each nonlinear node (`mul`,
    `select`) mints ONE fresh auxiliary variable and ONE bilinear constraint; `add`/`const`/
    `var` fold into linear combinations for free; each `assertIsEqual` becomes the linear
    constraint `(A_l − A_r)·1 = 0`. Aux variables live in the `Sum.inr` component of
    `RVar := Var ⊕ ℕ`, so the frontend witness is untouched (no offset arithmetic).
  * **`Circuit.extend`** — the canonical witness extension: the aux variables filled with
    their computed values (`assertsAux`, the mint-order value list).
  * **`gHolds`** — THE bridge: `c.satisfied a ↔ r1csSatisfied c.lower (c.extend a)`.
    Forward is completeness (an accepting frontend witness extends to a satisfying R1CS
    witness); backward rides **`lower_sound`**, the STRONGER soundness fact: ANY R1CS witness
    agreeing with `a` on the frontend variables forces acceptance — the minted constraints
    FORCE every aux value (`lowerWire_forces`), so a prover cannot cheat in the aux region.

Classified seam (named, NOT load-bearing here): `Fr` carries its `CommRing` structure — which
is ALL that R1CS satisfaction (`+`, `·` and the bilinear form) consumes; bilinearity is by
CONSTRUCTION of `LinComb`, not by a degree argument needing a field. The `Field Fr` upgrade
requires `Fact (Nat.Prime rBN254)`, and Mathlib's `norm_num` primality extension tops out
near 25 bits (`Mathlib/Tactic/NormNum/Prime.lean`) — a 254-bit Pratt-certificate chain
(`Mathlib.NumberTheory.LucasPrimality` is present) is the follow-up lane, needed only when
inverse/division gadgets (`api.Inverse`, `api.Div`) arrive. Nothing in this file's theorems
assumes primality.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Dregg2.Tactics

namespace Dregg2.Circuit.R1csFr

/-! ## §1 The field Fr — BN254 scalar field. -/

/-- The BN254 scalar-field modulus `r` (gnark `ecc.BN254.ScalarField`): the order of the
BN254 (alt_bn128) G1/G2 groups — the field the gnark frontend arithmetizes over. -/
def rBN254 : ℕ :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

/-- **Fr** — the BN254 scalar field as `ZMod rBN254`. `CommRing` (all R1CS satisfaction
uses) is automatic; `Nontrivial` from `1 < r` below. The `Field` upgrade is the named
primality-certificate seam in the header — consumed by NO theorem here. -/
abbrev Fr : Type := ZMod rBN254

instance : Fact (1 < rBN254) := ⟨by norm_num [rBN254]⟩

example : CommRing Fr := inferInstance
example : Nontrivial Fr := inferInstance

/-! ## §2 The frontend op-DAG (gnark-frontend shape). -/

/-- A frontend witness-variable index. -/
abbrev Var := ℕ

/-- The frontend witness: values for the frontend variables. -/
abbrev Assignment := Var → Fr

/-- **The gnark-frontend op-DAG.** `var`/`const` are leaves; `add`/`mul` the ring ops;
`select b x y` is gnark's `api.Select` — the field mux `b·(x−y)+y`, which equals
`if b = 1 then x else y` whenever `b` is boolean (`eval_select_of_bool`); gnark likewise
leaves booleanity of `b` to the caller (`api.AssertIsBoolean`). -/
inductive Wire where
  | var    : Var → Wire
  | const  : Fr → Wire
  | add    : Wire → Wire → Wire
  | mul    : Wire → Wire → Wire
  | select : Wire → Wire → Wire → Wire

/-- Frontend evaluation of a wire under a witness. -/
def Wire.eval : Wire → Assignment → Fr
  | .var v,        a => a v
  | .const c,      _ => c
  | .add x y,      a => x.eval a + y.eval a
  | .mul x y,      a => x.eval a * y.eval a
  | .select b x y, a => b.eval a * (x.eval a - y.eval a) + y.eval a

/-- On BOOLEAN selectors the mux is the genuine if-then-else (the gnark `Select` contract). -/
theorem Wire.eval_select_of_bool (b x y : Wire) (a : Assignment)
    (hb : b.eval a = 0 ∨ b.eval a = 1) :
    (Wire.select b x y).eval a = if b.eval a = 1 then x.eval a else y.eval a := by
  rcases hb with h | h <;> simp [Wire.eval, h, sub_add_cancel]

/-- **A frontend circuit**: the list of `assertIsEqual` pairs (the only constraint-adding
frontend op; `add`/`mul`/`select` just build wires). -/
structure Circuit where
  asserts : List (Wire × Wire)

/-- **Frontend acceptance** — every asserted pair evaluates equal under the witness. -/
def Circuit.satisfied (c : Circuit) (a : Assignment) : Prop :=
  ∀ p ∈ c.asserts, p.1.eval a = p.2.eval a

instance (c : Circuit) (a : Assignment) : Decidable (c.satisfied a) :=
  inferInstanceAs (Decidable (∀ p ∈ c.asserts, p.1.eval a = p.2.eval a))

/-! ## §3 R1CS over Fr — linear combinations and bilinear constraints. -/

/-- An R1CS wire index: `inl v` = a frontend witness variable, `inr i` = an auxiliary
variable minted by the lowering. Keeping aux vars in their own summand means the frontend
witness embeds unchanged — no offset arithmetic, no clobbering. -/
abbrev RVar := Var ⊕ ℕ

/-- The full R1CS witness vector `z` (frontend + aux). -/
abbrev RAssignment := RVar → Fr

/-- **A linear combination** `constTerm + Σ coeff·z(v)` — the `A`/`B`/`C` rows of R1CS
(the constant models the conventional fixed `1`-wire). Strictly linear BY CONSTRUCTION:
this is where the v1 ℤ-rail's unbounded `Expr` nesting is structurally forbidden. -/
structure LinComb where
  constTerm : Fr
  terms     : List (RVar × Fr)

namespace LinComb

/-- Evaluate the linear combination under a witness. -/
def eval (lc : LinComb) (z : RAssignment) : Fr :=
  lc.constTerm + (lc.terms.map fun t => t.2 * z t.1).sum

/-- The constant LC `c`. -/
def ofConst (c : Fr) : LinComb := ⟨c, []⟩

/-- The single-variable LC `1·z(v)`. -/
def ofVar (v : RVar) : LinComb := ⟨0, [(v, 1)]⟩

/-- LC addition (concatenate terms, add constants). -/
def add (l₁ l₂ : LinComb) : LinComb :=
  ⟨l₁.constTerm + l₂.constTerm, l₁.terms ++ l₂.terms⟩

/-- LC subtraction (negate the right terms). -/
def sub (l₁ l₂ : LinComb) : LinComb :=
  ⟨l₁.constTerm - l₂.constTerm, l₁.terms ++ l₂.terms.map fun t => (t.1, -t.2)⟩

@[simp] theorem eval_ofConst (c : Fr) (z : RAssignment) : (ofConst c).eval z = c := by
  simp [eval, ofConst]

@[simp] theorem eval_ofVar (v : RVar) (z : RAssignment) : (ofVar v).eval z = z v := by
  simp [eval, ofVar]

@[simp] theorem eval_add (l₁ l₂ : LinComb) (z : RAssignment) :
    (add l₁ l₂).eval z = l₁.eval z + l₂.eval z := by
  simp [eval, add, List.map_append, List.sum_append]; ring

private theorem sum_map_neg (l : List (RVar × Fr)) (z : RAssignment) :
    (l.map fun t => -t.2 * z t.1).sum = -(l.map fun t => t.2 * z t.1).sum := by
  induction l with
  | nil => simp
  | cons h t ih => simp only [List.map_cons, List.sum_cons, ih]; ring

@[simp] theorem eval_sub (l₁ l₂ : LinComb) (z : RAssignment) :
    (sub l₁ l₂).eval z = l₁.eval z - l₂.eval z := by
  have h : (l₂.terms.map fun t => (t.1, -t.2)).map (fun t => t.2 * z t.1)
      = l₂.terms.map fun t => -t.2 * z t.1 := by
    simp [List.map_map, Function.comp_def]
  simp only [eval, sub, List.map_append, List.sum_append, h, sum_map_neg]
  ring

end LinComb

/-- **One R1CS constraint** — the bilinear form `⟨A,z⟩ · ⟨B,z⟩ = ⟨C,z⟩`. Degree ≤ 2 by
TYPE: `A`/`B`/`C` are `LinComb`s, so no deeper nesting can be written. -/
structure R1c where
  A : LinComb
  B : LinComb
  C : LinComb

/-- The constraint holds under a witness. -/
def R1c.holds (c : R1c) (z : RAssignment) : Prop :=
  c.A.eval z * c.B.eval z = c.C.eval z

instance (c : R1c) (z : RAssignment) : Decidable (c.holds z) :=
  inferInstanceAs (Decidable (_ = _))

/-- An R1CS: the list of bilinear constraints. -/
abbrev R1cs := List R1c

/-- **R1CS satisfaction** — every constraint holds (the prover's claim to gnark). -/
def r1csSatisfied (cs : R1cs) (z : RAssignment) : Prop :=
  ∀ c ∈ cs, c.holds z

instance (cs : R1cs) (z : RAssignment) : Decidable (r1csSatisfied cs z) :=
  inferInstanceAs (Decidable (∀ c ∈ cs, c.holds z))

/-! ## §4 Lowering — the frontend compiles to R1CS.

Each `mul`/`select` node mints one fresh aux variable (`.inr n`) and one bilinear
constraint; linear structure folds into the `LinComb`. The counter `n` is the next fresh
aux index, threaded left-to-right. -/

/-- The result of lowering a wire: the LC denoting its value, the constraints minted, and
the next fresh aux index. -/
structure Lowered where
  out  : LinComb
  cs   : R1cs
  next : ℕ

/-- **Lower a wire to R1CS.** `mul x y` mints `aux := ⟨lx⟩·⟨ly⟩`; `select b x y` mints
`aux := ⟨lb⟩·(⟨lx⟩−⟨ly⟩)` and denotes `aux + ⟨ly⟩` — exactly the gnark decompositions. -/
def lowerWire : Wire → ℕ → Lowered
  | .var v,   n => ⟨.ofVar (.inl v), [], n⟩
  | .const c, n => ⟨.ofConst c, [], n⟩
  | .add x y, n =>
      let Lx := lowerWire x n
      let Ly := lowerWire y Lx.next
      ⟨Lx.out.add Ly.out, Lx.cs ++ Ly.cs, Ly.next⟩
  | .mul x y, n =>
      let Lx := lowerWire x n
      let Ly := lowerWire y Lx.next
      ⟨.ofVar (.inr Ly.next),
       Lx.cs ++ Ly.cs ++ [⟨Lx.out, Ly.out, .ofVar (.inr Ly.next)⟩],
       Ly.next + 1⟩
  | .select b x y, n =>
      let Lb := lowerWire b n
      let Lx := lowerWire x Lb.next
      let Ly := lowerWire y Lx.next
      ⟨(LinComb.ofVar (.inr Ly.next)).add Ly.out,
       Lb.cs ++ Lx.cs ++ Ly.cs ++ [⟨Lb.out, Lx.out.sub Ly.out, .ofVar (.inr Ly.next)⟩],
       Ly.next + 1⟩

/-- How many aux variables a wire mints (one per nonlinear node). -/
def Wire.auxCount : Wire → ℕ
  | .var _        => 0
  | .const _      => 0
  | .add x y      => x.auxCount + y.auxCount
  | .mul x y      => x.auxCount + y.auxCount + 1
  | .select b x y => b.auxCount + x.auxCount + y.auxCount + 1

/-- The aux VALUES a wire mints under witness `a`, in mint order — the semantic content of
the aux region (each `mul`/`select` node contributes its product value). -/
def auxVals (a : Assignment) : Wire → List Fr
  | .var _        => []
  | .const _      => []
  | .add x y      => auxVals a x ++ auxVals a y
  | .mul x y      => auxVals a x ++ auxVals a y ++ [x.eval a * y.eval a]
  | .select b x y =>
      auxVals a b ++ auxVals a x ++ auxVals a y ++
        [b.eval a * (x.eval a - y.eval a)]

theorem auxVals_length (a : Assignment) (w : Wire) :
    (auxVals a w).length = w.auxCount := by
  induction w <;> simp [auxVals, Wire.auxCount, *] <;> omega

/-- The counter advances by exactly the number of minted aux variables. -/
theorem lowerWire_next (w : Wire) (n : ℕ) : (lowerWire w n).next = n + w.auxCount := by
  induction w generalizing n with
  | var v => simp [lowerWire, Wire.auxCount]
  | const c => simp [lowerWire, Wire.auxCount]
  | add x y ihx ihy => simp only [lowerWire, Wire.auxCount, ihx, ihy]; omega
  | mul x y ihx ihy => simp only [lowerWire, Wire.auxCount, ihx, ihy]; omega
  | select b x y ihb ihx ihy =>
      simp only [lowerWire, Wire.auxCount, ihb, ihx, ihy]; omega

/-! ### getD-over-append plumbing (the aux region is a concatenation of subregions). -/

private theorem getD_append_lt {α : Type*} (xs ys : List α) (i : ℕ) (d : α)
    (h : i < xs.length) : (xs ++ ys).getD i d = xs.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private theorem getD_append_ge {α : Type*} (xs ys : List α) (i : ℕ) (d : α)
    (h : xs.length ≤ i) : (xs ++ ys).getD i d = ys.getD (i - xs.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

/-- Split an aux-region agreement over a concatenation into the two subregions. -/
private theorem aux_region_split (z : RAssignment) (n : ℕ) (xs ys : List Fr)
    (haux : ∀ i, i < (xs ++ ys).length → z (.inr (n + i)) = (xs ++ ys).getD i 0) :
    (∀ i, i < xs.length → z (.inr (n + i)) = xs.getD i 0) ∧
    (∀ i, i < ys.length → z (.inr (n + xs.length + i)) = ys.getD i 0) := by
  constructor
  · intro i hi
    have h1 := haux i (by simp only [List.length_append]; omega)
    rwa [getD_append_lt _ _ _ _ hi] at h1
  · intro i hi
    have h1 := haux (xs.length + i) (by simp only [List.length_append]; omega)
    rw [getD_append_ge _ _ _ _ (by omega)] at h1
    simp only [Nat.add_sub_cancel_left] at h1
    rw [show n + xs.length + i = n + (xs.length + i) by omega]
    exact h1

/-! ## §5 The two directions of the wire-level bridge. -/

/-- **Completeness (wire level).** If `z` agrees with the frontend witness on `inl` and
carries the canonical aux values on the wire's region, then the lowered LC evaluates to the
wire's frontend value and EVERY minted constraint holds. -/
theorem lowerWire_complete (a : Assignment) (z : RAssignment)
    (hinl : ∀ v, z (.inl v) = a v) :
    ∀ (w : Wire) (n : ℕ),
      (∀ i, i < (auxVals a w).length → z (.inr (n + i)) = (auxVals a w).getD i 0) →
      (lowerWire w n).out.eval z = w.eval a ∧ (∀ c ∈ (lowerWire w n).cs, c.holds z) := by
  intro w
  induction w with
  | var v =>
      intro n _
      exact ⟨by simp [lowerWire, Wire.eval, hinl], by intro c hc; simp [lowerWire] at hc⟩
  | const c =>
      intro n _
      exact ⟨by simp [lowerWire, Wire.eval], by intro c hc; simp [lowerWire] at hc⟩
  | add x y ihx ihy =>
      intro n haux
      simp only [auxVals] at haux
      obtain ⟨hxr, hyr0⟩ := aux_region_split z n _ _ haux
      have hnx : (lowerWire x n).next = n + (auxVals a x).length := by
        rw [lowerWire_next, auxVals_length]
      have hyr : ∀ i, i < (auxVals a y).length →
          z (.inr ((lowerWire x n).next + i)) = (auxVals a y).getD i 0 := by
        intro i hi; rw [hnx]; exact hyr0 i hi
      obtain ⟨hex, hcx⟩ := ihx n hxr
      obtain ⟨hey, hcy⟩ := ihy (lowerWire x n).next hyr
      constructor
      · simp [lowerWire, Wire.eval, hex, hey]
      · intro c hc
        simp only [lowerWire, List.mem_append] at hc
        rcases hc with h | h
        · exact hcx c h
        · exact hcy c h
  | mul x y ihx ihy =>
      intro n haux
      simp only [auxVals] at haux
      obtain ⟨h12, hm0⟩ := aux_region_split z n _ _ haux
      obtain ⟨hxr, hyr0⟩ := aux_region_split z n _ _ h12
      have hnx : (lowerWire x n).next = n + (auxVals a x).length := by
        rw [lowerWire_next, auxVals_length]
      have hyr : ∀ i, i < (auxVals a y).length →
          z (.inr ((lowerWire x n).next + i)) = (auxVals a y).getD i 0 := by
        intro i hi; rw [hnx]; exact hyr0 i hi
      obtain ⟨hex, hcx⟩ := ihx n hxr
      obtain ⟨hey, hcy⟩ := ihy (lowerWire x n).next hyr
      have hny : (lowerWire y (lowerWire x n).next).next
          = n + (auxVals a x ++ auxVals a y).length := by
        rw [lowerWire_next, hnx]
        simp only [List.length_append, auxVals_length]
        omega
      have hmint : z (.inr ((lowerWire y (lowerWire x n).next).next))
          = x.eval a * y.eval a := by
        have h0 := hm0 0 (by simp)
        rw [hny]
        simpa using h0
      constructor
      · simp only [lowerWire, LinComb.eval_ofVar]
        rw [hmint]
        simp [Wire.eval]
      · intro c hc
        simp only [lowerWire, List.mem_append, List.mem_singleton] at hc
        rcases hc with (h | h) | h
        · exact hcx c h
        · exact hcy c h
        · subst h
          simp only [R1c.holds, LinComb.eval_ofVar]
          rw [hex, hey, hmint]
  | select b x y ihb ihx ihy =>
      intro n haux
      simp only [auxVals] at haux
      obtain ⟨h123, hm0⟩ := aux_region_split z n _ _ haux
      obtain ⟨h12, hyr0⟩ := aux_region_split z n _ _ h123
      obtain ⟨hbr, hxr0⟩ := aux_region_split z n _ _ h12
      have hnb : (lowerWire b n).next = n + (auxVals a b).length := by
        rw [lowerWire_next, auxVals_length]
      have hxr : ∀ i, i < (auxVals a x).length →
          z (.inr ((lowerWire b n).next + i)) = (auxVals a x).getD i 0 := by
        intro i hi; rw [hnb]; exact hxr0 i hi
      have hnx : (lowerWire x (lowerWire b n).next).next
          = n + (auxVals a b ++ auxVals a x).length := by
        rw [lowerWire_next, hnb]
        simp only [List.length_append, auxVals_length]
        omega
      have hyr : ∀ i, i < (auxVals a y).length →
          z (.inr ((lowerWire x (lowerWire b n).next).next + i))
            = (auxVals a y).getD i 0 := by
        intro i hi; rw [hnx]; exact hyr0 i hi
      obtain ⟨heb, hcb⟩ := ihb n hbr
      obtain ⟨hex, hcx⟩ := ihx (lowerWire b n).next hxr
      obtain ⟨hey, hcy⟩ := ihy (lowerWire x (lowerWire b n).next).next hyr
      have hny : (lowerWire y (lowerWire x (lowerWire b n).next).next).next
          = n + (auxVals a b ++ auxVals a x ++ auxVals a y).length := by
        rw [lowerWire_next, hnx]
        simp only [List.length_append, auxVals_length]
        omega
      have hmint : z (.inr ((lowerWire y (lowerWire x (lowerWire b n).next).next).next))
          = b.eval a * (x.eval a - y.eval a) := by
        have h0 := hm0 0 (by simp)
        rw [hny]
        simpa using h0
      constructor
      · simp only [lowerWire, LinComb.eval_add, LinComb.eval_ofVar]
        rw [hmint, hey]
        simp [Wire.eval]
      · intro c hc
        simp only [lowerWire, List.mem_append, List.mem_singleton] at hc
        rcases hc with ((h | h) | h) | h
        · exact hcb c h
        · exact hcx c h
        · exact hcy c h
        · subst h
          simp only [R1c.holds, LinComb.eval_ofVar, LinComb.eval_sub]
          rw [heb, hex, hey, hmint]

/-- **Forcing (wire level — the soundness engine).** For ANY witness `z` agreeing with `a`
on the frontend variables, the minted constraints FORCE the lowered LC to the frontend
value — the aux region cannot be filled adversarially: each mul-constraint pins its aux
variable to the product of already-forced values. No freshness argument is even needed;
the constraints determine the values outright. -/
theorem lowerWire_forces (a : Assignment) (z : RAssignment)
    (hinl : ∀ v, z (.inl v) = a v) :
    ∀ (w : Wire) (n : ℕ),
      (∀ c ∈ (lowerWire w n).cs, c.holds z) →
      (lowerWire w n).out.eval z = w.eval a := by
  intro w
  induction w with
  | var v => intro n _; simp [lowerWire, Wire.eval, hinl]
  | const c => intro n _; simp [lowerWire, Wire.eval]
  | add x y ihx ihy =>
      intro n hsat
      have hx := ihx n (fun c hc => hsat c (by simp only [lowerWire, List.mem_append]; tauto))
      have hy := ihy (lowerWire x n).next
        (fun c hc => hsat c (by simp only [lowerWire, List.mem_append]; tauto))
      simp [lowerWire, Wire.eval, hx, hy]
  | mul x y ihx ihy =>
      intro n hsat
      have hx := ihx n (fun c hc => hsat c
        (by simp only [lowerWire, List.mem_append, List.mem_singleton]; tauto))
      have hy := ihy (lowerWire x n).next (fun c hc => hsat c
        (by simp only [lowerWire, List.mem_append, List.mem_singleton]; tauto))
      have hcon := hsat
        ⟨(lowerWire x n).out, (lowerWire y (lowerWire x n).next).out,
         .ofVar (.inr (lowerWire y (lowerWire x n).next).next)⟩
        (by simp only [lowerWire, List.mem_append, List.mem_singleton]; tauto)
      simp only [R1c.holds, LinComb.eval_ofVar] at hcon
      simp only [lowerWire, LinComb.eval_ofVar, Wire.eval]
      rw [← hcon, hx, hy]
  | select b x y ihb ihx ihy =>
      intro n hsat
      have hb := ihb n (fun c hc => hsat c
        (by simp only [lowerWire, List.mem_append, List.mem_singleton]; tauto))
      have hx := ihx (lowerWire b n).next (fun c hc => hsat c
        (by simp only [lowerWire, List.mem_append, List.mem_singleton]; tauto))
      have hy := ihy (lowerWire x (lowerWire b n).next).next (fun c hc => hsat c
        (by simp only [lowerWire, List.mem_append, List.mem_singleton]; tauto))
      have hcon := hsat
        ⟨(lowerWire b n).out,
         (lowerWire x (lowerWire b n).next).out.sub
           (lowerWire y (lowerWire x (lowerWire b n).next).next).out,
         .ofVar (.inr (lowerWire y (lowerWire x (lowerWire b n).next).next).next)⟩
        (by simp only [lowerWire, List.mem_append, List.mem_singleton]; tauto)
      simp only [R1c.holds, LinComb.eval_ofVar, LinComb.eval_sub] at hcon
      simp only [lowerWire, LinComb.eval_add, LinComb.eval_ofVar, Wire.eval]
      rw [← hcon, hb, hx, hy]

/-! ## §6 Circuit-level lowering + the canonical witness extension. -/

/-- Lower the assert list: each `assertIsEqual (l, r)` contributes both wires' minted
constraints plus the linear equality constraint `(⟨A_l⟩ − ⟨A_r⟩)·1 = 0`. -/
def lowerAsserts : List (Wire × Wire) → ℕ → R1cs
  | [], _ => []
  | (l, r) :: rest, n =>
      let Ll := lowerWire l n
      let Lr := lowerWire r Ll.next
      Ll.cs ++ Lr.cs ++ [⟨Ll.out.sub Lr.out, .ofConst 1, .ofConst 0⟩]
        ++ lowerAsserts rest Lr.next

/-- **The R1CS of a circuit.** -/
def Circuit.lower (c : Circuit) : R1cs := lowerAsserts c.asserts 0

/-- The circuit-level aux value list (mint order, across all asserts). -/
def assertsAux (a : Assignment) : List (Wire × Wire) → List Fr
  | [] => []
  | (l, r) :: rest => auxVals a l ++ auxVals a r ++ assertsAux a rest

/-- **The canonical witness extension**: the frontend witness on `inl`, the computed aux
values on `inr` (out-of-range aux defaults to `0` — no constraint mentions those). -/
def Circuit.extend (c : Circuit) (a : Assignment) : RAssignment := fun v =>
  match v with
  | .inl v => a v
  | .inr i => (assertsAux a c.asserts).getD i 0

/-- **Completeness (circuit level).** An aux-region-respecting witness extending an
ACCEPTING frontend witness satisfies the whole lowered R1CS. -/
theorem lowerAsserts_complete (a : Assignment) (z : RAssignment)
    (hinl : ∀ v, z (.inl v) = a v) :
    ∀ (ps : List (Wire × Wire)) (n : ℕ),
      (∀ i, i < (assertsAux a ps).length → z (.inr (n + i)) = (assertsAux a ps).getD i 0) →
      (∀ p ∈ ps, p.1.eval a = p.2.eval a) →
      ∀ c ∈ lowerAsserts ps n, c.holds z := by
  intro ps
  induction ps with
  | nil => intro n _ _ c hc; simp [lowerAsserts] at hc
  | cons q rest ih =>
      obtain ⟨l, r⟩ := q
      intro n haux hacc c hc
      simp only [assertsAux] at haux
      obtain ⟨h12, hrest0⟩ := aux_region_split z n _ _ haux
      obtain ⟨hlr, hrr0⟩ := aux_region_split z n _ _ h12
      have hnl : (lowerWire l n).next = n + (auxVals a l).length := by
        rw [lowerWire_next, auxVals_length]
      have hrr : ∀ i, i < (auxVals a r).length →
          z (.inr ((lowerWire l n).next + i)) = (auxVals a r).getD i 0 := by
        intro i hi; rw [hnl]; exact hrr0 i hi
      have hcl := lowerWire_complete a z hinl l n hlr
      have hcr := lowerWire_complete a z hinl r (lowerWire l n).next hrr
      have haccl : l.eval a = r.eval a := hacc (l, r) List.mem_cons_self
      simp only [lowerAsserts, List.mem_append, List.mem_singleton] at hc
      rcases hc with ((h | h) | h) | h
      · exact hcl.2 c h
      · exact hcr.2 c h
      · subst h
        simp only [R1c.holds, LinComb.eval_sub, LinComb.eval_ofConst, mul_one]
        rw [hcl.1, hcr.1, haccl, sub_self]
      · have hnr : (lowerWire r (lowerWire l n).next).next
            = n + (auxVals a l ++ auxVals a r).length := by
          rw [lowerWire_next, hnl]
          simp only [List.length_append, auxVals_length]
          omega
        have hrest : ∀ i, i < (assertsAux a rest).length →
            z (.inr ((lowerWire r (lowerWire l n).next).next + i))
              = (assertsAux a rest).getD i 0 := by
          intro i hi; rw [hnr]; exact hrest0 i hi
        exact ih (lowerWire r (lowerWire l n).next).next hrest
          (fun p hp => hacc p (List.mem_cons_of_mem _ hp)) c h

/-- **Forcing (circuit level).** ANY R1CS witness agreeing with `a` on the frontend
variables and satisfying the lowered system forces every asserted pair equal. -/
theorem lowerAsserts_forces (a : Assignment) (z : RAssignment)
    (hinl : ∀ v, z (.inl v) = a v) :
    ∀ (ps : List (Wire × Wire)) (n : ℕ),
      (∀ c ∈ lowerAsserts ps n, c.holds z) →
      ∀ p ∈ ps, p.1.eval a = p.2.eval a := by
  intro ps
  induction ps with
  | nil => intro n _ p hp; simp at hp
  | cons q rest ih =>
      obtain ⟨l, r⟩ := q
      intro n hsat p hp
      have hfl := lowerWire_forces a z hinl l n (fun c hc => hsat c
        (by simp only [lowerAsserts, List.mem_append, List.mem_singleton]; tauto))
      have hfr := lowerWire_forces a z hinl r (lowerWire l n).next (fun c hc => hsat c
        (by simp only [lowerAsserts, List.mem_append, List.mem_singleton]; tauto))
      rcases List.mem_cons.mp hp with heq | hp'
      · subst heq
        have heqc := hsat
          ⟨(lowerWire l n).out.sub (lowerWire r (lowerWire l n).next).out,
           .ofConst 1, .ofConst 0⟩
          (by simp only [lowerAsserts, List.mem_append, List.mem_singleton]; tauto)
        simp only [R1c.holds, LinComb.eval_sub, LinComb.eval_ofConst, mul_one] at heqc
        rw [hfl, hfr] at heqc
        exact sub_eq_zero.mp heqc
      · exact ih (lowerWire r (lowerWire l n).next).next (fun c hc => hsat c
          (by simp only [lowerAsserts, List.mem_append, List.mem_singleton]; tauto)) p hp'

/-! ## §7 THE BRIDGE — `gHolds` and the strong soundness form. -/

/-- **Strong soundness.** ANY R1CS witness for the lowered circuit that agrees with `a` on
the frontend variables — however the prover filled the aux region — forces frontend
acceptance. This is the form the gnark verifier story consumes: the R1CS admits no
satisfying assignment over a non-accepting frontend witness. -/
theorem lower_sound (c : Circuit) (a : Assignment) (z : RAssignment)
    (hinl : ∀ v, z (.inl v) = a v) (hsat : r1csSatisfied c.lower z) :
    c.satisfied a :=
  lowerAsserts_forces a z hinl c.asserts 0 hsat

/-- **`gHolds` — the deliverable.** The frontend accepts the witness `a` IFF the lowered
R1CS is satisfied by the canonical extended witness. Forward is completeness (compute the
aux values, every bilinear constraint holds); backward is soundness via `lower_sound`
(the extension agrees with `a` on frontend variables by definition). -/
theorem gHolds (c : Circuit) (a : Assignment) :
    c.satisfied a ↔ r1csSatisfied c.lower (c.extend a) := by
  constructor
  · intro hacc cn hcn
    exact lowerAsserts_complete a (c.extend a) (fun _ => rfl) c.asserts 0
      (fun i _ => by rw [Nat.zero_add]; rfl) hacc cn hcn
  · intro hsat
    exact lower_sound c a (c.extend a) (fun _ => rfl) hsat

#assert_axioms lowerWire_complete
#assert_axioms lowerWire_forces
#assert_axioms lowerAsserts_complete
#assert_axioms lowerAsserts_forces
#assert_axioms lower_sound
#assert_axioms gHolds
#assert_axioms Wire.eval_select_of_bool

/-! ## §8 Teeth — non-vacuity on a concrete a·b = c circuit (and a select mux).

The trivial gnark circuit `assertIsEqual(mul(a, b), c)`: satisfied by `3·5 = 15`, refuted
by `3·5 ≠ 14` — at BOTH levels (frontend `satisfied`, lowered `r1csSatisfied`), so the
bridge is exercised on a witness it accepts AND one it rejects. -/

/-- `a·b = c` — `assertIsEqual (mul (var 0) (var 1)) (var 2)`. -/
def mulCircuit : Circuit := ⟨[(.mul (.var 0) (.var 1), .var 2)]⟩

/-- The CORRECT witness `a=3, b=5, c=15`. -/
def goodA : Assignment := fun v =>
  if v = 0 then 3 else if v = 1 then 5 else if v = 2 then 15 else 0

/-- The WRONG witness `a=3, b=5, c=14`. -/
def badA : Assignment := fun v =>
  if v = 0 then 3 else if v = 1 then 5 else if v = 2 then 14 else 0

-- Frontend: accepted / refuted.
#guard mulCircuit.satisfied goodA
#guard ¬ mulCircuit.satisfied badA
-- R1CS: the lowered system is satisfied by the correct extended witness, refuted by the
-- wrong one (the aux var carries 3·5 = 15 either way; the equality constraint kills 14).
#guard r1csSatisfied mulCircuit.lower (mulCircuit.extend goodA)
#guard ¬ r1csSatisfied mulCircuit.lower (mulCircuit.extend badA)

/-- The lowered `mulCircuit` is exactly TWO bilinear constraints: the minted
`⟨a⟩·⟨b⟩ = aux` and the assert `(aux − c)·1 = 0`. -/
example : mulCircuit.lower.length = 2 := rfl

/-- `select` mux teeth: `assertIsEqual (select (var 0) (var 1) (var 2)) (var 3)`. -/
def selCircuit : Circuit := ⟨[(.select (.var 0) (.var 1) (.var 2), .var 3)]⟩

-- b = 1 selects x (= 7); b = 0 selects y (= 9); the crossed claim is refuted.
#guard selCircuit.satisfied
  (fun v => if v = 0 then 1 else if v = 1 then 7 else if v = 2 then 9 else 7)
#guard selCircuit.satisfied
  (fun v => if v = 0 then 0 else if v = 1 then 7 else if v = 2 then 9 else 9)
#guard ¬ selCircuit.satisfied
  (fun v => if v = 0 then 0 else if v = 1 then 7 else if v = 2 then 9 else 7)
-- …and the same through the lowering (select mints one aux + one bilinear constraint).
#guard r1csSatisfied selCircuit.lower (selCircuit.extend
  (fun v => if v = 0 then 1 else if v = 1 then 7 else if v = 2 then 9 else 7))
#guard ¬ r1csSatisfied selCircuit.lower (selCircuit.extend
  (fun v => if v = 0 then 0 else if v = 1 then 7 else if v = 2 then 9 else 7))

end Dregg2.Circuit.R1csFr

/-
# Dregg2.Metatheory.FOLArithmetizationCorrected

A positive, carrier-parametric core for zero-means-true arithmetization.

The important distinction is explicit in the type of the theorem:

* conjunction-as-addition is valid only on a distinguished class of `good`
  residuals for which good summands cannot cancel;
* disjunction-as-multiplication additionally needs the absence of zero
  divisors on good residuals.

Gabbay's rational construction inhabits this interface with
`good q := 0 <= q`.  An unconstrained finite field does not.  Two exact
finite-field repairs are proved below:

* compile a natural-number residual, prove a static `< p` bound, and only then
  cast it to `ZMod p` (the no-wrap route already used elsewhere in dregg);
* convert each atomic residual to a Boolean false-bit using two constraints
  and an inverse witness, then use Boolean polynomials for all connectives.

Bounded quantifiers are represented by finite conjunction/disjunction folds.
This is the executable first-order fragment: the range is statement-fixed,
not witness-selected.  Random linear batching is deliberately not redefined
here: `Circuit.OodSoundnessGame.batchResidual` and `rlc_debatch` already prove
the needed post-commit Schwartz--Zippel de-batching theorem.

Standalone positive artifact; no central import is modified.
-/
import Dregg2.Tactics
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith

namespace Dregg2.Metatheory.FOLArithmetizationCorrected

/-! ## 1. The exact algebraic contract -/

/-- Laws needed by zero-means-true arithmetic.  `good` is load-bearing: for
the rational model it means nonnegative.  Requiring the laws only on `good`
values avoids the false claim that addition is conjunction on every element
of a ring. -/
structure ZeroTrueLaws (R : Type*) [Semiring R] where
  good : R -> Prop
  zero_good : good 0
  one_good : good 1
  add_good : forall {a b}, good a -> good b -> good (a + b)
  mul_good : forall {a b}, good a -> good b -> good (a * b)
  add_eq_zero_iff : forall {a b}, good a -> good b ->
    (a + b = 0 <-> a = 0 /\ b = 0)
  mul_eq_zero_iff : forall {a b}, good a -> good b ->
    (a * b = 0 <-> a = 0 \/ b = 0)

/-- The positive Boolean fragment.  Bounded first-order quantifiers compile
to the finite folds `all` and `any` below. -/
inductive PositiveFormula (Atom : Type*) where
  | top
  | bottom
  | atom (a : Atom)
  | and (p q : PositiveFormula Atom)
  | or (p q : PositiveFormula Atom)
  deriving Repr

namespace PositiveFormula

/-- Ordinary logical semantics, independent of the arithmetic carrier. -/
def Holds {Atom : Type*} (truth : Atom -> Prop) : PositiveFormula Atom -> Prop
  | .top => True
  | .bottom => False
  | .atom a => truth a
  | .and p q => Holds truth p /\ Holds truth q
  | .or p q => Holds truth p \/ Holds truth q

/-- Zero-means-true compilation: `and` is addition; `or` is multiplication. -/
def residual {Atom R : Type*} [Semiring R] (atomResidual : Atom -> R) :
    PositiveFormula Atom -> R
  | .top => 0
  | .bottom => 1
  | .atom a => atomResidual a
  | .and p q => residual atomResidual p + residual atomResidual q
  | .or p q => residual atomResidual p * residual atomResidual q

/-- Every compiled residual remains in the protected `good` class. -/
theorem residual_good {Atom R : Type*} [Semiring R] (laws : ZeroTrueLaws R)
    (atomResidual : Atom -> R) (hatom : forall a, laws.good (atomResidual a)) :
    forall p, laws.good (residual atomResidual p) := by
  intro p
  induction p with
  | top => exact laws.zero_good
  | bottom => exact laws.one_good
  | atom a => exact hatom a
  | and p q ihp ihq => exact laws.add_good ihp ihq
  | or p q ihp ihq => exact laws.mul_good ihp ihq

/-- **Exact compiler theorem.**  If each atom is zero exactly when it is true
and every atom residual is `good`, then the compiled polynomial is zero
exactly when the source formula holds. -/
theorem residual_eq_zero_iff {Atom R : Type*} [Semiring R] [Nontrivial R]
    (laws : ZeroTrueLaws R) (truth : Atom -> Prop) (atomResidual : Atom -> R)
    (hatomGood : forall a, laws.good (atomResidual a))
    (hatomCorrect : forall a, atomResidual a = 0 <-> truth a) :
    forall p, residual atomResidual p = 0 <-> Holds truth p := by
  intro p
  induction p with
  | top => simp [residual, Holds]
  | bottom => simp [residual, Holds]
  | atom a => simpa [residual, Holds] using hatomCorrect a
  | and p q ihp ihq =>
      rw [residual, Holds,
        laws.add_eq_zero_iff
          (residual_good laws atomResidual hatomGood p)
          (residual_good laws atomResidual hatomGood q), ihp, ihq]
  | or p q ihp ihq =>
      rw [residual, Holds,
        laws.mul_eq_zero_iff
          (residual_good laws atomResidual hatomGood p)
          (residual_good laws atomResidual hatomGood q), ihp, ihq]

/-- Finite universal quantification after grounding its statement-fixed range. -/
def all {Atom : Type*} : List (PositiveFormula Atom) -> PositiveFormula Atom
  | [] => .top
  | p :: ps => .and p (all ps)

/-- Finite existential quantification after grounding its statement-fixed range. -/
def any {Atom : Type*} : List (PositiveFormula Atom) -> PositiveFormula Atom
  | [] => .bottom
  | p :: ps => .or p (any ps)

theorem holds_all {Atom : Type*} (truth : Atom -> Prop) (ps : List (PositiveFormula Atom)) :
    Holds truth (all ps) <-> forall p, p ∈ ps -> Holds truth p := by
  induction ps with
  | nil => simp [all, Holds]
  | cons p ps ih => simp [all, Holds, ih]

theorem holds_any {Atom : Type*} (truth : Atom -> Prop) (ps : List (PositiveFormula Atom)) :
    Holds truth (any ps) <-> exists p, p ∈ ps /\ Holds truth p := by
  induction ps with
  | nil => simp [any, Holds]
  | cons p ps ih => simp [any, Holds, ih]

/-- Exact bounded-universal compiler corollary. -/
theorem residual_all_eq_zero_iff {Atom R : Type*} [Semiring R] [Nontrivial R]
    (laws : ZeroTrueLaws R) (truth : Atom -> Prop) (atomResidual : Atom -> R)
    (hatomGood : forall a, laws.good (atomResidual a))
    (hatomCorrect : forall a, atomResidual a = 0 <-> truth a)
    (ps : List (PositiveFormula Atom)) :
    residual atomResidual (all ps) = 0 <->
      forall p, p ∈ ps -> Holds truth p := by
  rw [residual_eq_zero_iff laws truth atomResidual hatomGood hatomCorrect, holds_all]

/-- Exact bounded-existential compiler corollary. -/
theorem residual_any_eq_zero_iff {Atom R : Type*} [Semiring R] [Nontrivial R]
    (laws : ZeroTrueLaws R) (truth : Atom -> Prop) (atomResidual : Atom -> R)
    (hatomGood : forall a, laws.good (atomResidual a))
    (hatomCorrect : forall a, atomResidual a = 0 <-> truth a)
    (ps : List (PositiveFormula Atom)) :
    residual atomResidual (any ps) = 0 <->
      exists p, p ∈ ps /\ Holds truth p := by
  rw [residual_eq_zero_iff laws truth atomResidual hatomGood hatomCorrect, holds_any]

end PositiveFormula

/-! ## 2. Characteristic-zero and exact-natural instances -/

/-- Gabbay's intended carrier contract: rational residuals protected by a
nonnegativity invariant. -/
def nonnegativeRationalLaws : ZeroTrueLaws Rat where
  good q := 0 <= q
  zero_good := by norm_num
  one_good := by norm_num
  add_good := by intro a b ha hb; exact add_nonneg ha hb
  mul_good := by intro a b ha hb; exact mul_nonneg ha hb
  add_eq_zero_iff := by
    intro a b ha hb
    constructor
    · intro h
      constructor <;> linarith
    · rintro ⟨rfl, rfl⟩
      simp
  mul_eq_zero_iff := by
    intro a b _ _
    exact mul_eq_zero

/-- Naturals are an exact zero-truth carrier.  This is useful as the source
semantics for the no-wrap field compilation below. -/
def naturalLaws : ZeroTrueLaws Nat where
  good _ := True
  zero_good := trivial
  one_good := trivial
  add_good := by intros; trivial
  mul_good := by intros; trivial
  add_eq_zero_iff := by intros; exact Nat.add_eq_zero_iff
  mul_eq_zero_iff := by intros; exact Nat.mul_eq_zero

/-! ## 3. Finite-field repair A: prove no-wrap before casting -/

/-- A natural below the modulus has zero residue exactly when it is literally
zero.  The `< p` bound is the complete no-wrap obligation for this residual. -/
theorem zmod_natCast_eq_zero_iff_of_lt {p n : Nat} (hbound : n < p) :
    ((n : ZMod p) = 0) <-> n = 0 := by
  constructor
  · intro hzero
    have hzero' : (n : ZMod p) = ((0 : Nat) : ZMod p) := by
      simpa using hzero
    have hmod : n % p = 0 % p :=
      (ZMod.natCast_eq_natCast_iff' n 0 p).mp hzero'
    simpa [Nat.mod_eq_of_lt hbound] using hmod
  · rintro rfl
    simp

/-- **No-wrap compiler theorem.**  Compile first into exact naturals; a static
bound on the complete residual then makes the field gate equivalent to the
source formula. -/
theorem natural_residual_cast_sound {Atom : Type*} {p : Nat}
    (truth : Atom -> Prop) (atomResidual : Atom -> Nat)
    (hatomCorrect : forall a, atomResidual a = 0 <-> truth a)
    (formula : PositiveFormula Atom)
    (hbound : PositiveFormula.residual atomResidual formula < p) :
    ((↑(PositiveFormula.residual atomResidual formula) : ZMod p) = 0) <->
      PositiveFormula.Holds truth formula := by
  rw [zmod_natCast_eq_zero_iff_of_lt hbound]
  exact PositiveFormula.residual_eq_zero_iff naturalLaws truth atomResidual
    (fun _ => trivial) hatomCorrect formula

/-! ## 4. Finite-field repair B: witnessed Boolean false-bits -/

/-- Two constraints turn an arbitrary field residual `r` into a false-bit `b`:

* `r * (1 - b) = 0` forces `b = 1` when `r` is nonzero;
* `r * inv = b` forces `b = 0` when `r` is zero and supplies the inverse in
  the nonzero case.

Thus `b = 0` means the atom is true. -/
structure FalseBitWitness {F : Type*} [Field F] (r b inv : F) : Prop where
  force_nonzero : r * (1 - b) = 0
  define_bit : r * inv = b

/-- The two witness constraints are sound: zero false-bit iff zero residual. -/
theorem falseBit_eq_zero_iff {F : Type*} [Field F] {r b inv : F}
    (h : FalseBitWitness r b inv) : b = 0 <-> r = 0 := by
  constructor
  · intro hb
    simpa [hb] using h.force_nonzero
  · intro hr
    simpa [hr] using h.define_bit.symm

/-- The same constraints force the output into `{0,1}`; a separate Booleanity
constraint is unnecessary over a field. -/
theorem falseBit_is_bit {F : Type*} [Field F] {r b inv : F}
    (h : FalseBitWitness r b inv) : b = 0 \/ b = 1 := by
  by_cases hr : r = 0
  · exact Or.inl ((falseBit_eq_zero_iff h).2 hr)
  · right
    have hrest : 1 - b = 0 := (mul_eq_zero.mp h.force_nonzero).resolve_left hr
    exact (sub_eq_zero.mp hrest).symm

/-- Completeness: every residual has a false-bit and inverse witness. -/
theorem exists_falseBitWitness {F : Type*} [Field F] (r : F) :
    exists b inv, FalseBitWitness r b inv := by
  by_cases hr : r = 0
  · refine ⟨0, 0, ?_⟩
    constructor <;> simp [hr]
  · refine ⟨1, r⁻¹, ?_⟩
    constructor
    · simp
    · simpa [hr]

/-- Boolean false-bit conjunction: source `and` is false when either input is
false, hence Boolean OR. -/
def falseAnd {F : Type*} [Ring F] (a b : F) : F := a + b - a * b

/-- Boolean false-bit disjunction: source `or` is false only when both inputs
are false, hence Boolean AND. -/
def falseOr {F : Type*} [Mul F] (a b : F) : F := a * b

/-- Boolean false-bit negation. -/
def falseNot {F : Type*} [Ring F] (a : F) : F := 1 - a

def IsBit {F : Type*} [Zero F] [One F] (a : F) : Prop := a = 0 \/ a = 1

theorem falseAnd_is_bit {F : Type*} [Ring F] {a b : F}
    (ha : IsBit a) (hb : IsBit b) : IsBit (falseAnd a b) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    simp [IsBit, falseAnd]

theorem falseOr_is_bit {F : Type*} [Ring F] {a b : F}
    (ha : IsBit a) (hb : IsBit b) : IsBit (falseOr a b) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    simp [IsBit, falseOr]

theorem falseNot_is_bit {F : Type*} [Ring F] {a : F}
    (ha : IsBit a) : IsBit (falseNot a) := by
  rcases ha with rfl | rfl <;> simp [IsBit, falseNot]

theorem falseAnd_eq_zero_iff {F : Type*} [Ring F] [Nontrivial F] {a b : F}
    (ha : IsBit a) (hb : IsBit b) : falseAnd a b = 0 <-> a = 0 /\ b = 0 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    simp [falseAnd]

theorem falseOr_eq_zero_iff {F : Type*} [Ring F] [IsDomain F] {a b : F}
    (_ha : IsBit a) (_hb : IsBit b) : falseOr a b = 0 <-> a = 0 \/ b = 0 := by
  simp [falseOr]

theorem falseNot_eq_zero_iff {F : Type*} [Ring F] [Nontrivial F] {a : F}
    (ha : IsBit a) : falseNot a = 0 <-> a ≠ 0 := by
  rcases ha with rfl | rfl <;> simp [falseNot]

/-! A full Boolean core after atom Booleanization. -/

inductive BooleanFormula (Atom : Type*) where
  | top
  | bottom
  | atom (a : Atom)
  | and (p q : BooleanFormula Atom)
  | or (p q : BooleanFormula Atom)
  | not (p : BooleanFormula Atom)
  deriving Repr

namespace BooleanFormula

def Holds {Atom : Type*} (truth : Atom -> Prop) : BooleanFormula Atom -> Prop
  | .top => True
  | .bottom => False
  | .atom a => truth a
  | .and p q => Holds truth p /\ Holds truth q
  | .or p q => Holds truth p \/ Holds truth q
  | .not p => Not (Holds truth p)

/-- Compile an already-Booleanized atom map to one Boolean false-bit. -/
def falseBit {Atom F : Type*} [Ring F] (atomBit : Atom -> F) :
    BooleanFormula Atom -> F
  | .top => 0
  | .bottom => 1
  | .atom a => atomBit a
  | .and p q => falseAnd (falseBit atomBit p) (falseBit atomBit q)
  | .or p q => falseOr (falseBit atomBit p) (falseBit atomBit q)
  | .not p => falseNot (falseBit atomBit p)

/-- **Exact field compiler theorem after atom Booleanization.**  The result is
itself a bit, and it is zero exactly when the source formula holds.  Unlike the
raw sum construction, this permits negation and cannot suffer cancellation. -/
theorem falseBit_correct {Atom F : Type*} [Field F]
    (truth : Atom -> Prop) (atomBit : Atom -> F)
    (hatomBit : forall a, IsBit (atomBit a))
    (hatomCorrect : forall a, atomBit a = 0 <-> truth a) :
    forall p, IsBit (falseBit atomBit p) /\
      (falseBit atomBit p = 0 <-> Holds truth p) := by
  intro p
  induction p with
  | top => simp [falseBit, Holds, IsBit]
  | bottom => simp [falseBit, Holds, IsBit]
  | atom a => exact ⟨hatomBit a, hatomCorrect a⟩
  | and p q ihp ihq =>
      refine ⟨falseAnd_is_bit ihp.1 ihq.1, ?_⟩
      rw [falseBit, Holds, falseAnd_eq_zero_iff ihp.1 ihq.1, ihp.2, ihq.2]
  | or p q ihp ihq =>
      refine ⟨falseOr_is_bit ihp.1 ihq.1, ?_⟩
      rw [falseBit, Holds, falseOr_eq_zero_iff ihp.1 ihq.1, ihp.2, ihq.2]
  | not p ihp =>
      refine ⟨falseNot_is_bit ihp.1, ?_⟩
      rw [falseBit, Holds, falseNot_eq_zero_iff ihp.1]
      exact not_congr ihp.2

end BooleanFormula

#assert_all_clean [
  PositiveFormula.residual_good,
  PositiveFormula.residual_eq_zero_iff,
  PositiveFormula.holds_all,
  PositiveFormula.holds_any,
  PositiveFormula.residual_all_eq_zero_iff,
  PositiveFormula.residual_any_eq_zero_iff,
  zmod_natCast_eq_zero_iff_of_lt,
  natural_residual_cast_sound,
  falseBit_eq_zero_iff,
  falseBit_is_bit,
  exists_falseBitWitness,
  falseAnd_is_bit,
  falseOr_is_bit,
  falseNot_is_bit,
  falseAnd_eq_zero_iff,
  falseOr_eq_zero_iff,
  falseNot_eq_zero_iff,
  BooleanFormula.falseBit_correct]

end Dregg2.Metatheory.FOLArithmetizationCorrected

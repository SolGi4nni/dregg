/-
# Dregg2.Crypto.Deriv.SymbolicAffine — ADDITIVE covers for the AFFINE / QF-LIA guard atoms:
finite `allowedTransitions` state-machine guards (EXACT, unbounded) and BOUNDED-DOMAIN affine
guards (`affineLe`/`affineEq`/`sumEquals`, and — over the difference encoding — the two-frame
`affineDeltaLe`/`sumEqualsAcross`), plugged into the minterm tower with ZERO tower changes.

This module takes the plug-in point `SymbolicMintermsPlus` priced ("any future witness machinery
plugs in as a new `coverOfAtoms`-style constructor") and closes two LIA-flavored classes the
per-(field,value)-pin covers cannot reach:

## §A — EASY WIN: `allowedTransitions f allowed` (EXACT, no bound).

`allowedTransitions f allowed` reads the pair `(old[f], new[f])` and admits iff it lies in the
FINITE pair set `allowed`. For a guard whose every leaf is exactly `allowedTransitions f allowed`
(the SAME `f`, `allowed`) under `and`/`or`/`not` (`atOnly`), the single-frame truth is a function of
the ONE bit `atBit f allowed a` ("the transition is allowed"). Two candidate frames then cover every
minterm: `atYes` — the head allowed pair, encoded through the two-frame `transitionSymbol` envelope
(old = `{f ↦ p₁}`, new = `{f ↦ p₂}`) — and `atNo` = the empty record (fails closed). This is a
GENUINELY FINITE, TOTAL `MintermCover`: bounded state-machine guards decide with NO domain bound.
(`f` must avoid the two reserved envelope field names — real authored fields do.)

## §B — THE AFFINE COVER: BOUNDED-DOMAIN affine guards (`affineLe`/`affineEq`/`sumEquals`).

⚠ BOUNDARY, stated plainly: this is a decision for AFFINE GUARDS OVER BOUNDED-DOMAIN FIELDS, NOT the
general linear-integer-arithmetic feasibility problem. A single unbounded affine atom already has NO
finite minterm cover for the RAW predicate: `affineEq [(1,"x")] 100` is satisfiable only OFF any box
`[lo,hi] ⊊ {100}`, so an in-box witness list cannot realize the satisfied signature over ALL frames
(the `MintermCover.covers` obligation is TOTAL — `∀ a`, not `∀ in-box a`). The honest resolution:
the decided guard CONJOINS the raw affine atoms with explicit `inRangeTwoSided` DOMAIN GATES on every
mentioned field (`boxAffineLeaf`, built from REAL atoms). Off the box a domain gate fails, so the
whole leaf reads `false`; on the box the affine sum is one of finitely many values. The leaf is then
a function of the finite `boxSig` observable (per field: its in-box value, or `none` for
absent/out-of-box), and the FULL GRID of in-box assignments — `boxCands`, a `List.sections` product,
the exact-value twin of `SymbolicIntervals.scalarCands` — realizes every `boxSig`, giving a TOTAL,
finite `MintermCover`. SOUNDNESS is unconditional (every witness is a real frame). `sumEquals fields
value = affineEq (fields.map ((1,·))) value`, so it rides the SAME cover.

The general (unbounded) case is the NAMED RESIDUAL: it needs the integer-feasibility box theorem
"a feasible system of affine constraints has a witness inside a box computed from the coefficients"
(the LIA a-priori bound — Papadimitriou-style), which is NOT proven here. The two-frame
`affineDeltaLeField` (bound READ from a state slot) further interacts the rate field with the box and
is left to the difference-encoding extension — NAMED, not faked.

## Runnability cost.

The grid `boxCands lo hi flds` has `(|[lo,hi]| + 1)^|flds|` frames; the `#guard`s below therefore use
TINY boxes and ≤ 2 fields. No `#guard` kernel-reduces a `Decidable` INSTANCE (the 64GB/20min
anti-pattern of the sibling modules); demonstrations are CHEAP `emptyFix` Boolean evaluations only.

`#assert_all_clean` at the bottom; `sorry`-free.
-/
import Dregg2.Crypto.Deriv.SymbolicMintermsPlus
import Dregg2.Crypto.Deriv.SymbolicIntervals

namespace Dregg2.Crypto.Deriv

open Dregg2.Exec
open Dregg2.Exec.PredAlgebra
open PredRE (der null derives leaf bot derList derives_eq_null_derList
  predBEq RigidFull rigidRE transitionSymbol symbolOld transitionTagField transitionOldField)

/-! ## §A `allowedTransitions` — the finite state-machine cover. -/

/-- **`atBit f allowed a`** — the ONE observable an `allowedTransitions f allowed`-algebra guard
reads: is the transition `(old[f], new[f])` in the finite pair set `allowed`. -/
def atBit (f : FieldName) (allowed : List (Int × Int)) (a : Value) : Bool :=
  leaf (.atom (.allowedTransitions f allowed)) a

/-- **`atOnly f allowed φ`** — every atom of `φ` is exactly `allowedTransitions f allowed` (under
`and`/`or`/`not`, with `tt`/`ff`). Anything else fails closed. -/
def atOnly (f : FieldName) (allowed : List (Int × Int)) : Pred → Bool
  | .tt => true
  | .ff => true
  | .atom (.allowedTransitions f' allowed') => f' == f && allowed' == allowed
  | .and l r => atOnly f allowed l && atOnly f allowed r
  | .or l r  => atOnly f allowed l && atOnly f allowed r
  | .not p   => atOnly f allowed p
  | _ => false

/-- An `atOnly` leaf reads a frame ONLY through `atBit` — the factoring that makes two candidate
frames a complete minterm cover. -/
theorem atOnly_reads {f : FieldName} {allowed : List (Int × Int)} :
    ∀ {φ : Pred}, atOnly f allowed φ = true →
    ∀ {a b : Value}, atBit f allowed a = atBit f allowed b → leaf φ a = leaf φ b
  | .tt, _, _, _, _ => rfl
  | .ff, _, _, _, _ => rfl
  | .atom (.allowedTransitions f' allowed'), h, a, b, hab => by
      simp only [atOnly, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hab
  | .and l r, h, a, b, hab => by
      simp only [atOnly, Bool.and_eq_true] at h
      have ihl := atOnly_reads (φ := l) h.1 hab
      have ihr := atOnly_reads (φ := r) h.2 hab
      simp only [leaf, Pred.eval] at ihl ihr ⊢
      rw [ihl, ihr]
  | .or l r, h, a, b, hab => by
      simp only [atOnly, Bool.and_eq_true] at h
      have ihl := atOnly_reads (φ := l) h.1 hab
      have ihr := atOnly_reads (φ := r) h.2 hab
      simp only [leaf, Pred.eval] at ihl ihr ⊢
      rw [ihl, ihr]
  | .not p, h, a, b, hab => by
      have ih := atOnly_reads (φ := p) h hab
      simp only [leaf, Pred.eval] at ih ⊢
      rw [ih]

/-- The violating witness: the empty record (absent field ⇒ `allowedTransitions` fails closed). -/
def atNo : Value := .record []

/-- The satisfying witness: the head allowed pair `(p₁, p₂)`, encoded as a `transitionSymbol` whose
OLD frame reads `p₁` and NEW frame reads `p₂` at `f`. Degenerates to `atNo` for empty `allowed`. -/
def atYes (f : FieldName) (allowed : List (Int × Int)) : Value :=
  match allowed with
  | [] => atNo
  | (p1, p2) :: _ => transitionSymbol (.record [(f, .int p1)]) (.record [(f, .int p2)])

theorem atBit_no (f : FieldName) (allowed : List (Int × Int)) : atBit f allowed atNo = false := rfl

theorem atBit_empty (f : FieldName) (a : Value) : atBit f [] a = false := by
  simp only [atBit, leaf, Pred.eval, evalConstraint]
  cases (symbolOld a).scalar f <;> cases a.scalar f <;> rfl

theorem atBit_yes {f : FieldName} {allowed : List (Int × Int)} (hne : allowed ≠ [])
    (hf1 : f ≠ transitionTagField) (hf2 : f ≠ transitionOldField) :
    atBit f allowed (atYes f allowed) = true := by
  cases allowed with
  | nil => exact absurd rfl hne
  | cons p rest =>
      obtain ⟨p1, p2⟩ := p
      have hold : (symbolOld (atYes f ((p1, p2) :: rest))).scalar f = some p1 := by
        have he : symbolOld (atYes f ((p1, p2) :: rest)) = .record [(f, .int p1)] := by
          simp only [atYes, transitionSymbol, symbolOld, beq_self_eq_true, Bool.and_self,
            if_true]
        rw [he]
        simp only [Value.scalar, Value.field]
        rw [List.find?_cons_of_pos (by simp)]
        rfl
      have hnew : (atYes f ((p1, p2) :: rest)).scalar f = some p2 := by
        simp only [atYes, transitionSymbol, Value.scalar, Value.field]
        rw [List.find?_cons_of_neg (by simp only [beq_iff_eq]; exact fun h => hf1 h.symm),
            List.find?_cons_of_neg (by simp only [beq_iff_eq]; exact fun h => hf2 h.symm),
            List.find?_cons_of_pos (by simp)]
        rfl
      simp only [atBit, leaf, Pred.eval, evalConstraint, hold, hnew,
        List.any_cons, beq_self_eq_true, Bool.and_self, Bool.true_or]

/-- **`coverOfAllowedTransitions`** — the assembled cover: the head-pair witness `atYes` and the
empty record `atNo` hit every minterm of an `allowedTransitions f allowed`-algebra guard (each
frame's whole signature is a function of its `atBit`, and the two candidates realize both bits). -/
def coverOfAllowedTransitions (f : FieldName) (allowed : List (Int × Int))
    (hf1 : f ≠ transitionTagField) (hf2 : f ≠ transitionOldField)
    (L : List Pred) (hL : ∀ φ ∈ L, atOnly f allowed φ = true) : MintermCover L where
  cands := [atYes f allowed, atNo]
  covers a := by
    cases hb : atBit f allowed a with
    | false =>
        refine ⟨atNo, by simp, ?_⟩
        exact List.map_inj_left.mpr fun φ hφ =>
          atOnly_reads (hL φ hφ) (by rw [atBit_no, hb])
    | true =>
        have hne : allowed ≠ [] := by
          rintro rfl
          rw [atBit_empty] at hb
          exact Bool.false_ne_true hb
        refine ⟨atYes f allowed, by simp, ?_⟩
        exact List.map_inj_left.mpr fun φ hφ =>
          atOnly_reads (hL φ hφ) (by rw [atBit_yes hne hf1 hf2, hb])

/-- **`atRE f allowed R`** — every leaf of `R` is in the `allowedTransitions f allowed` algebra. -/
def atRE (f : FieldName) (allowed : List (Int × Int)) : PredRE → Bool
  | .ε         => true
  | .sym φ     => atOnly f allowed φ
  | .alt a b   => atRE f allowed a && atRE f allowed b
  | .inter a b => atRE f allowed a && atRE f allowed b
  | .cat a b   => atRE f allowed a && atRE f allowed b
  | .star a    => atRE f allowed a
  | .neg a     => atRE f allowed a

theorem atRE_leaves {f : FieldName} {allowed : List (Int × Int)} :
    ∀ {R : PredRE}, atRE f allowed R = true → ∀ φ ∈ leavesOf R, atOnly f allowed φ = true := by
  intro R
  induction R with
  | ε => intro _ φ hφ; simp [leavesOf] at hφ
  | sym ψ => intro h φ hφ; rw [List.mem_singleton.mp hφ]; exact h
  | alt l r ihl ihr =>
      intro h φ hφ
      simp only [atRE, Bool.and_eq_true] at h
      simp only [leavesOf, List.mem_append] at hφ
      rcases hφ with hφ | hφ
      · exact ihl h.1 φ hφ
      · exact ihr h.2 φ hφ
  | inter l r ihl ihr =>
      intro h φ hφ
      simp only [atRE, Bool.and_eq_true] at h
      simp only [leavesOf, List.mem_append] at hφ
      rcases hφ with hφ | hφ
      · exact ihl h.1 φ hφ
      · exact ihr h.2 φ hφ
  | cat l r ihl ihr =>
      intro h φ hφ
      simp only [atRE, Bool.and_eq_true] at h
      simp only [leavesOf, List.mem_append] at hφ
      rcases hφ with hφ | hφ
      · exact ihl h.1 φ hφ
      · exact ihr h.2 φ hφ
  | star r ih => intro h φ hφ; exact ih h φ hφ
  | neg r ih => intro h φ hφ; exact ih h φ hφ

theorem atRE_symDiff {f : FieldName} {allowed : List (Int × Int)} {R S : PredRE}
    (hR : atRE f allowed R = true) (hS : atRE f allowed S = true) :
    atRE f allowed (symDiff R S) = true := by
  simp only [symDiff, atRE, Bool.and_eq_true]
  exact ⟨⟨hR, hS⟩, hR, hS⟩

/-- `atOnly` leaves are `predBEq`-reflexive (`atom` leaves ride `DecidableEq StateConstraint`) —
rigidity is derivable on this fragment. -/
theorem predBEq_refl_of_atOnly {f : FieldName} {allowed : List (Int × Int)} :
    ∀ {φ : Pred}, atOnly f allowed φ = true → predBEq φ φ = true
  | .tt, _ => rfl
  | .ff, _ => rfl
  | .atom (.allowedTransitions _ _), _ => by simp [predBEq]
  | .and l r, h => by
      simp only [atOnly, Bool.and_eq_true] at h
      simp only [predBEq, Bool.and_eq_true]
      exact ⟨predBEq_refl_of_atOnly h.1, predBEq_refl_of_atOnly h.2⟩
  | .or l r, h => by
      simp only [atOnly, Bool.and_eq_true] at h
      simp only [predBEq, Bool.and_eq_true]
      exact ⟨predBEq_refl_of_atOnly h.1, predBEq_refl_of_atOnly h.2⟩
  | .not p, h => by
      simpa [predBEq] using predBEq_refl_of_atOnly (φ := p) h

theorem rigidRE_of_atRE {f : FieldName} {allowed : List (Int × Int)} {R : PredRE}
    (h : atRE f allowed R = true) : RigidFull R :=
  rigidRE_of_leaves fun φ hφ => predBEq_refl_of_atOnly (atRE_leaves h φ hφ)

/-- **`predRE_emptiness_decidable_at`** — runnable unbounded emptiness for state-machine guards:
the two-frame allowed-pair cover through the generic assembly. -/
def predRE_emptiness_decidable_at (fuel : Nat) (f : FieldName) (allowed : List (Int × Int))
    (hf1 : f ≠ transitionTagField) (hf2 : f ≠ transitionOldField) {R : PredRE}
    (h : atRE f allowed R = true) : Decidable (∃ w, derives w R = true) :=
  predRE_emptiness_decidable_cover
    (coverOfAllowedTransitions f allowed hf1 hf2 (leavesOf R) (atRE_leaves h))
    fuel (symbolicOver_leavesOf R) (rigidRE_of_atRE h)

/-- **`predRE_equivalence_decidable_at`** — runnable language equivalence for state-machine guards. -/
def predRE_equivalence_decidable_at (fuel : Nat) (f : FieldName) (allowed : List (Int × Int))
    (hf1 : f ≠ transitionTagField) (hf2 : f ≠ transitionOldField) {R S : PredRE}
    (hR : atRE f allowed R = true) (hS : atRE f allowed S = true) :
    Decidable (∀ w, derives w R = derives w S) :=
  predRE_equivalence_decidable_cover
    (coverOfAllowedTransitions f allowed hf1 hf2 (leavesOf (symDiff R S))
      (atRE_leaves (atRE_symDiff hR hS)))
    fuel (symbolicOver_leavesOf _) (rigidRE_of_atRE (atRE_symDiff hR hS))

/-! ## §A guards — the state-machine class KERNEL-RUNS (cheap `emptyFix`, both polarities). -/

section AllowedGuards

/-- A status machine: only `0→1` and `1→2` transitions permitted. -/
def statusMachineRE : PredRE := .sym (.atom (.allowedTransitions "status" [(0, 1), (1, 2)]))

/-- The self-contradiction: an allowed transition AND its negation on one frame. -/
def statusContraRE : PredRE :=
  .inter statusMachineRE (.sym (.not (.atom (.allowedTransitions "status" [(0, 1), (1, 2)]))))

-- Fragment membership + rigidity, kernel-checked:
#guard atRE "status" [(0, 1), (1, 2)] statusMachineRE = true
#guard atRE "status" [(0, 1), (1, 2)] statusContraRE = true
#guard rigidRE statusMachineRE = true
-- A guard MIXING two different allowed-lists on the field is NOT in the fragment — fails closed:
#guard atOnly "status" [(0, 1)] (.atom (.allowedTransitions "status" [(0, 1), (1, 2)])) = false

/-- The candidate list the state-machine decisions run on: head-pair witness + empty record. -/
def statusCands : List Value := [atYes "status" [(0, 1), (1, 2)], atNo]

-- SATISFIABLE: a permitted transition exists (some allowed pair) — `emptyFix = some false`:
#guard emptyFix statusCands 32 statusMachineRE = some false
-- EMPTY at ALL lengths: the self-contradiction admits no word — `emptyFix = some true`:
#guard emptyFix statusCands 32 statusContraRE = some true
-- Bit-level: the head pair `(0,1)` is allowed, a not-listed pair `(5,9)` is refused:
#guard atBit "status" [(0, 1), (1, 2)]
  (transitionSymbol (.record [("status", .int 0)]) (.record [("status", .int 1)])) = true
#guard atBit "status" [(0, 1), (1, 2)]
  (transitionSymbol (.record [("status", .int 5)]) (.record [("status", .int 9)])) = false

end AllowedGuards

/-! ## §B The bounded-domain affine cover.

The observable is `boxSig lo hi flds a` — per mentioned field, its in-box value (or `none` for
absent/out-of-box). A leaf that FACTORS through `boxSig` (`BoxReads`) is covered by the full in-box
grid `boxCands`. The affine atoms `affineLe`/`affineEq`, CONJOINED with `inRangeTwoSided` domain
gates on every mentioned field (`boxAffineLe`/`boxAffineEq`), are proven `BoxReads`. -/

/-- `[v, v+1, …, v+(n-1)]` — the fuel-counted integer run (no `List.map`/coercion HO-unification). -/
def boxValsAux : Nat → Int → List Int
  | 0,     _ => []
  | n + 1, v => v :: boxValsAux n (v + 1)

/-- The integer domain `[lo, hi]` as a finite list. -/
def boxVals (lo hi : Int) : List Int := boxValsAux (hi - lo + 1).toNat lo

theorem mem_boxValsAux : ∀ {n : Nat} {v x : Int}, v ≤ x → x < v + n → x ∈ boxValsAux n v
  | 0, v, x, h1, h2 => by exact absurd h1 (by simp only [Nat.cast_zero, add_zero] at h2; omega)
  | n + 1, v, x, h1, h2 => by
      simp only [boxValsAux, List.mem_cons]
      by_cases hx : x = v
      · exact Or.inl hx
      · refine Or.inr (mem_boxValsAux (v := v + 1) (by omega) ?_)
        push_cast at h2 ⊢; omega

theorem mem_boxVals {lo hi x : Int} (h1 : lo ≤ x) (h2 : x ≤ hi) : x ∈ boxVals lo hi := by
  unfold boxVals
  refine mem_boxValsAux h1 ?_
  have e : ((hi - lo + 1).toNat : Int) = hi - lo + 1 := Int.toNat_of_nonneg (by omega)
  rw [e]; omega

/-- The in-box read of field `f` on frame `a`: its value when present AND in `[lo,hi]`, else `none`
(so absent and out-of-box collapse to the same observation). -/
def boxChoice (lo hi : Int) (a : Value) (f : FieldName) : Option Int :=
  match a.scalar f with
  | some x => if lo ≤ x ∧ x ≤ hi then some x else none
  | none => none

theorem boxChoice_in_box {lo hi : Int} {a : Value} {f : FieldName} {x : Int}
    (h : boxChoice lo hi a f = some x) : (lo ≤ x ∧ x ≤ hi) ∧ a.scalar f = some x := by
  unfold boxChoice at h
  split at h
  · rename_i y hs
    split at h
    · rename_i hb
      injection h with h; subst h; exact ⟨hb, hs⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem boxChoice_of_scalar {lo hi : Int} {a : Value} {f : FieldName} {x : Int}
    (hs : a.scalar f = some x) (hb : lo ≤ x ∧ x ≤ hi) : boxChoice lo hi a f = some x := by
  simp only [boxChoice, hs]
  rw [if_pos hb]

/-- The finite per-field signature: each mentioned field's in-box read. Two frames with equal
`boxSig` are indistinguishable by every `BoxReads` leaf. -/
def boxSig (lo hi : Int) (flds : List FieldName) (a : Value) : List (Option Int) :=
  flds.map (boxChoice lo hi a)

theorem boxSig_mem {lo hi : Int} {flds : List FieldName} {a b : Value}
    (h : boxSig lo hi flds a = boxSig lo hi flds b) {f : FieldName} (hf : f ∈ flds) :
    boxChoice lo hi a f = boxChoice lo hi b f :=
  List.map_inj_left.mp h f hf

/-- **`BoxReads lo hi flds φ`** — `φ`'s single-frame truth is a function of `boxSig lo hi flds`. -/
def BoxReads (lo hi : Int) (flds : List FieldName) (φ : Pred) : Prop :=
  ∀ a b : Value, boxSig lo hi flds a = boxSig lo hi flds b → leaf φ a = leaf φ b

theorem boxReads_tt {lo hi flds} : BoxReads lo hi flds .tt := fun _ _ _ => rfl
theorem boxReads_ff {lo hi flds} : BoxReads lo hi flds .ff := fun _ _ _ => rfl

theorem boxReads_and {lo hi flds} {l r : Pred}
    (hl : BoxReads lo hi flds l) (hr : BoxReads lo hi flds r) :
    BoxReads lo hi flds (.and l r) := fun a b hab => by
  have hlv := hl a b hab; have hrv := hr a b hab
  simp only [leaf, Pred.eval] at hlv hrv ⊢; rw [hlv, hrv]

theorem boxReads_or {lo hi flds} {l r : Pred}
    (hl : BoxReads lo hi flds l) (hr : BoxReads lo hi flds r) :
    BoxReads lo hi flds (.or l r) := fun a b hab => by
  have hlv := hl a b hab; have hrv := hr a b hab
  simp only [leaf, Pred.eval] at hlv hrv ⊢; rw [hlv, hrv]

theorem boxReads_not {lo hi flds} {p : Pred}
    (hp : BoxReads lo hi flds p) : BoxReads lo hi flds (.not p) := fun a b hab => by
  have hpv := hp a b hab
  simp only [leaf, Pred.eval] at hpv ⊢; rw [hpv]

/-! ### The domain gate and the gated affine atoms. -/

/-- The conjunction of `inRangeTwoSided f lo hi` domain gates over every mentioned field. -/
def rangeGates (lo hi : Int) : List FieldName → Pred
  | [] => .tt
  | f :: fs => .and (.atom (.simple (.inRangeTwoSided f lo hi))) (rangeGates lo hi fs)

theorem boxChoice_isSome_iff {lo hi : Int} {a : Value} {f : FieldName} :
    (boxChoice lo hi a f).isSome = true ↔ ∃ x, a.scalar f = some x ∧ lo ≤ x ∧ x ≤ hi := by
  constructor
  · intro h
    cases hx : boxChoice lo hi a f with
    | none => rw [hx] at h; exact absurd h (by simp)
    | some x => obtain ⟨hb, hs⟩ := boxChoice_in_box hx; exact ⟨x, hs, hb.1, hb.2⟩
  · rintro ⟨x, hs, h1, h2⟩; rw [boxChoice_of_scalar hs ⟨h1, h2⟩]; rfl

/-- The single domain gate reads a frame through `boxChoice`. -/
theorem leaf_inRange {lo hi : Int} {f : FieldName} {a : Value} :
    leaf (.atom (.simple (.inRangeTwoSided f lo hi))) a = (boxChoice lo hi a f).isSome := by
  have hiff := evalSimple_inRangeTwoSided_iff f lo hi (symbolOld a) a
  cases hB : (boxChoice lo hi a f).isSome with
  | true =>
      have : evalSimple (.inRangeTwoSided f lo hi) (symbolOld a) a = true :=
        hiff.mpr (boxChoice_isSome_iff.mp hB)
      simpa only [leaf, Pred.eval, evalConstraint] using this
  | false =>
      have hneg : ¬ (∃ x, a.scalar f = some x ∧ lo ≤ x ∧ x ≤ hi) := by
        intro h; rw [boxChoice_isSome_iff.mpr h] at hB; exact Bool.noConfusion hB
      have : evalSimple (.inRangeTwoSided f lo hi) (symbolOld a) a = false := by
        by_contra hc; rw [Bool.not_eq_false] at hc; exact hneg (hiff.mp hc)
      simpa only [leaf, Pred.eval, evalConstraint] using this

/-- The gate holds on `a` iff every mentioned field reads in-box. -/
theorem leaf_rangeGates {lo hi : Int} {flds : List FieldName} {a : Value} :
    leaf (rangeGates lo hi flds) a = (boxSig lo hi flds a).all Option.isSome := by
  induction flds with
  | nil => rfl
  | cons f fs ih =>
      have e : leaf (rangeGates lo hi (f :: fs)) a
          = (leaf (.atom (.simple (.inRangeTwoSided f lo hi))) a && leaf (rangeGates lo hi fs) a) := by
        simp only [rangeGates, leaf, Pred.eval]
      rw [e, leaf_inRange, ih]
      simp only [boxSig, List.map_cons, List.all_cons]

/-- `boxSig` equality transfers the gate truth. -/
theorem boxReads_rangeGates {lo hi : Int} (flds : List FieldName) :
    BoxReads lo hi flds (rangeGates lo hi flds) := fun a b hab => by
  rw [leaf_rangeGates, leaf_rangeGates, hab]

theorem affineSum_congr {a b : Value} : ∀ {terms : List (Int × FieldName)},
    (∀ t ∈ terms, a.scalar t.2 = b.scalar t.2) → affineSum a terms = affineSum b terms
  | [], _ => rfl
  | t :: ts, h => by
      have ha : affineSum a (t :: ts)
          = match affineSum a ts, a.scalar t.2 with
            | some s, some x => some (s + t.1 * x) | _, _ => none := rfl
      have hb : affineSum b (t :: ts)
          = match affineSum b ts, b.scalar t.2 with
            | some s, some x => some (s + t.1 * x) | _, _ => none := rfl
      rw [ha, hb, affineSum_congr (fun t' ht' => h t' (List.mem_cons_of_mem _ ht')),
          h t (by simp)]

/-- Under the gate, `boxSig` pins every mentioned field's exact value. -/
theorem scalar_of_gate {lo hi : Int} {flds : List FieldName} {a b : Value}
    (hab : boxSig lo hi flds a = boxSig lo hi flds b)
    (hga : leaf (rangeGates lo hi flds) a = true) {f : FieldName} (hf : f ∈ flds) :
    a.scalar f = b.scalar f := by
  rw [leaf_rangeGates, List.all_eq_true] at hga
  have hsome := hga (boxChoice lo hi a f) (List.mem_map.mpr ⟨f, hf, rfl⟩)
  cases hca : boxChoice lo hi a f with
  | none => rw [hca] at hsome; simp at hsome
  | some x =>
      obtain ⟨_, hax⟩ := boxChoice_in_box hca
      have hcb : boxChoice lo hi b f = some x := by rw [← boxSig_mem hab hf, hca]
      obtain ⟨_, hbx⟩ := boxChoice_in_box hcb
      rw [hax, hbx]

/-- **`boxAffineLe lo hi flds terms c`** — the REAL `affineLe terms c` atom conjoined with the
domain gates on `flds`. Decidable, and a genuine `BoxReads` leaf when the term-fields sit in `flds`. -/
def boxAffineLe (lo hi : Int) (flds : List FieldName) (terms : List (Int × FieldName)) (c : Int) :
    Pred := .and (rangeGates lo hi flds) (.atom (.affineLe terms c))

/-- **`boxAffineEq lo hi flds terms c`** — the gated `affineEq terms c`. -/
def boxAffineEq (lo hi : Int) (flds : List FieldName) (terms : List (Int × FieldName)) (c : Int) :
    Pred := .and (rangeGates lo hi flds) (.atom (.affineEq terms c))

theorem boxReads_affineLe {lo hi : Int} {flds : List FieldName} {terms : List (Int × FieldName)}
    {c : Int} (hsub : ∀ t ∈ terms, t.2 ∈ flds) :
    BoxReads lo hi flds (boxAffineLe lo hi flds terms c) := fun a b hab => by
  simp only [boxAffineLe, leaf, Pred.eval]
  have hg := boxReads_rangeGates flds a b hab
  simp only [leaf] at hg
  rw [hg]
  by_cases hgb : (rangeGates lo hi flds).eval (symbolOld b) b = true
  · have hga : (rangeGates lo hi flds).eval (symbolOld a) a = true := by rw [hg]; exact hgb
    have hsc : affineSum a terms = affineSum b terms :=
      affineSum_congr fun t ht => scalar_of_gate hab hga (hsub t ht)
    simp only [evalConstraint, hsc]
  · simp only [Bool.not_eq_true] at hgb
    rw [hgb]; simp

theorem boxReads_affineEq {lo hi : Int} {flds : List FieldName} {terms : List (Int × FieldName)}
    {c : Int} (hsub : ∀ t ∈ terms, t.2 ∈ flds) :
    BoxReads lo hi flds (boxAffineEq lo hi flds terms c) := fun a b hab => by
  simp only [boxAffineEq, leaf, Pred.eval]
  have hg := boxReads_rangeGates flds a b hab
  simp only [leaf] at hg
  rw [hg]
  by_cases hgb : (rangeGates lo hi flds).eval (symbolOld b) b = true
  · have hga : (rangeGates lo hi flds).eval (symbolOld a) a = true := by rw [hg]; exact hgb
    have hsc : affineSum a terms = affineSum b terms :=
      affineSum_congr fun t ht => scalar_of_gate hab hga (hsub t ht)
    simp only [evalConstraint, hsc]
  · simp only [Bool.not_eq_true] at hgb
    rw [hgb]; simp

/-! ### The grid enumeration → a total `MintermCover`. -/

/-- The candidate frame for `a`: the record pinning every mentioned field to its in-box read. -/
def boxFrame (lo hi : Int) (flds : List FieldName) (a : Value) : Value :=
  .record (flds.filterMap (fun f => (boxChoice lo hi a f).map (fun x => (f, Value.int x))))

/-- The full in-box grid: one record per choice of absent-or-in-box-value per mentioned field. -/
def boxCands (lo hi : Int) (flds : List FieldName) : List Value :=
  (((flds.map (fun f => (none :: (boxVals lo hi).map some).map (fun o => (f, o)))).sections).map
    (fun ch => .record (ch.filterMap (fun p => p.2.map (fun x => (p.1, Value.int x))))))

theorem boxFrame_scalar {lo hi : Int} {flds : List FieldName} (hnd : flds.Nodup) (a : Value)
    {f : FieldName} (hf : f ∈ flds) : (boxFrame lo hi flds a).scalar f = boxChoice lo hi a f :=
  scalar_ofChoices (g := boxChoice lo hi a) hnd hf

/-- The candidate for `a` reproduces `a`'s signature (in-box reads round-trip). -/
theorem boxSig_boxFrame {lo hi : Int} {flds : List FieldName} (hnd : flds.Nodup) (a : Value) :
    boxSig lo hi flds (boxFrame lo hi flds a) = boxSig lo hi flds a := by
  apply List.map_congr_left
  intro f hf
  have hsc := boxFrame_scalar (lo := lo) (hi := hi) hnd a hf
  cases hca : boxChoice lo hi a f with
  | none => rw [hca] at hsc; simp only [boxChoice, hsc]
  | some x =>
      rw [hca] at hsc
      obtain ⟨hb, _⟩ := boxChoice_in_box hca
      simp only [boxChoice, hsc, if_pos hb]

theorem boxFrame_mem_boxCands {lo hi : Int} (flds : List FieldName) (a : Value) :
    boxFrame lo hi flds a ∈ boxCands lo hi flds := by
  apply List.mem_map.mpr
  refine ⟨flds.map (fun f => (f, boxChoice lo hi a f)), ?_, ?_⟩
  · apply List.mem_sections.mpr
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    apply List.forall₂_same.mpr
    intro f _
    simp only [List.mem_map]
    refine ⟨boxChoice lo hi a f, ?_, rfl⟩
    cases hca : boxChoice lo hi a f with
    | none => exact List.mem_cons.mpr (Or.inl rfl)
    | some x =>
        obtain ⟨⟨h1, h2⟩, _⟩ := boxChoice_in_box hca
        exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨x, mem_boxVals h1 h2, rfl⟩))
  · simp only [boxFrame, List.filterMap_map]
    rfl

/-- **`coverOfBoxAffine`** — the assembled total `MintermCover` for any leaf list that factors
through `boxSig`: the in-box grid `boxCands` hits every minterm (the witness for frame `a` is its
in-box canonicalization `boxFrame a`, whose `boxSig` matches `a`'s). -/
def coverOfBoxAffine (lo hi : Int) (flds : List FieldName) (hnd : flds.Nodup) (L : List Pred)
    (hL : ∀ φ ∈ L, BoxReads lo hi flds φ) : MintermCover L where
  cands := boxCands lo hi flds
  covers a := by
    refine ⟨boxFrame lo hi flds a, boxFrame_mem_boxCands flds a, ?_⟩
    apply List.map_inj_left.mpr
    intro φ hφ
    exact hL φ hφ _ _ (boxSig_boxFrame hnd a)

/-! ### §B guards — bounded-domain affine, cheap `emptyFix`, both polarities.

TINY boxes (`[0,3]`, ≤ 2 fields) keep the grid — and thus the `emptyFix` search — small. -/

section AffineGuards

/-- Budget-delta band `out_a + out_b ≤ 5`, gated to `[0,3]²` — SATISFIABLE (e.g. `1 + 1`). -/
def budgetRE : PredRE := .sym (boxAffineLe 0 3 ["out_a", "out_b"] [(1, "out_a"), (1, "out_b")] 5)

/-- Price band `a + b ≤ 4`, gated to `[0,3]²` — SATISFIABLE. -/
def priceBandRE : PredRE := .sym (boxAffineLe 0 3 ["a", "b"] [(1, "a"), (1, "b")] 4)

/-- An affine CONTRADICTION over the box: `a + b ≤ 3 ∧ a + b ≥ 10` (the `≥` as `-a - b ≤ -10`),
gated to `[0,3]²` — EMPTY at all lengths (no in-box assignment; the box maxes `a+b` at 6). -/
def contraRE : PredRE :=
  .inter (.sym (boxAffineLe 0 3 ["a", "b"] [(1, "a"), (1, "b")] 3))
         (.sym (boxAffineLe 0 3 ["a", "b"] [(-1, "a"), (-1, "b")] (-10)))

/-- A conservation equation `inp = out` (`inp - out = 0`), gated to `[0,3]²` — SATISFIABLE. -/
def consvRE : PredRE := .sym (boxAffineEq 0 3 ["inp", "out"] [(1, "inp"), (-1, "out")] 0)

-- The `BoxReads` witnesses (kernel-checked term membership) confirm the leaves are in the fragment:
example : BoxReads 0 3 ["out_a", "out_b"]
    (boxAffineLe 0 3 ["out_a", "out_b"] [(1, "out_a"), (1, "out_b")] 5) :=
  @boxReads_affineLe 0 3 ["out_a", "out_b"] [(1, "out_a"), (1, "out_b")] 5 (by decide)
example : BoxReads 0 3 ["a", "b"] (boxAffineEq 0 3 ["a", "b"] [(1, "a"), (-1, "b")] 0) :=
  @boxReads_affineEq 0 3 ["a", "b"] [(1, "a"), (-1, "b")] 0 (by decide)

/-- **`predRE_emptiness_decidable_box`** — runnable unbounded emptiness for a bounded-domain affine
guard: the in-box grid cover through the generic assembly. `BoxReads`-per-leaf and rigidity are the
honest obligations (each leaf is a gated affine composite of REAL atoms). -/
def predRE_emptiness_decidable_box (lo hi : Int) (flds : List FieldName) (hnd : flds.Nodup)
    (fuel : Nat) {R : PredRE} (hL : ∀ φ ∈ leavesOf R, BoxReads lo hi flds φ)
    (hrig : RigidFull R) : Decidable (∃ w, derives w R = true) :=
  predRE_emptiness_decidable_cover (coverOfBoxAffine lo hi flds hnd (leavesOf R) hL)
    fuel (symbolicOver_leavesOf R) hrig

-- The candidate grid for a `[0,3]²` two-field guard: (none|0|1|2|3)² = 25 frames.
#guard (boxCands 0 3 ["a", "b"]).length = 25

-- SATISFIABLE budget/price/conservation guards — `emptyFix = some false`:
#guard emptyFix (boxCands 0 3 ["out_a", "out_b"]) 400 budgetRE = some false
#guard emptyFix (boxCands 0 3 ["a", "b"]) 400 priceBandRE = some false
#guard emptyFix (boxCands 0 3 ["inp", "out"]) 400 consvRE = some false
-- EMPTY affine contradiction at ALL lengths — `emptyFix = some true`:
#guard emptyFix (boxCands 0 3 ["a", "b"]) 400 contraRE = some true

end AffineGuards

/-! ## Axiom hygiene — §A + §B. -/

#assert_all_clean [
  atOnly_reads, atBit_no, atBit_empty, atBit_yes, coverOfAllowedTransitions,
  atRE_leaves, atRE_symDiff, predBEq_refl_of_atOnly, rigidRE_of_atRE,
  predRE_emptiness_decidable_at, predRE_equivalence_decidable_at,
  mem_boxVals, boxChoice_in_box, boxReads_and, boxReads_or, boxReads_not,
  leaf_rangeGates, boxReads_rangeGates, affineSum_congr, scalar_of_gate,
  boxReads_affineLe, boxReads_affineEq,
  boxSig_boxFrame, boxFrame_mem_boxCands, coverOfBoxAffine, predRE_emptiness_decidable_box
]

end Dregg2.Crypto.Deriv

/-
# Dregg2.Circuit.Emit.MinaOpeningCheckWeld — the WELD: the predicate the emitted AIR forces is
the predicate the REAL BLOCK satisfies.

## The failure mode this file exists to refuse

`PastaMsmAir.openingCheck_forces` proves the emitted gates force `msm(terms) + delta = O`. That
is a true theorem — and a true theorem about the WRONG predicate reads exactly like success. A
lowering found in this tree on 2026-07-27 asserted that `C_i` VANISHES at ζ: provable, and
useless. Nothing in `PastaMsmAir` alone rules out its reference MSM being a different function
from the one `SRS::verify` actually checks, or being one that no honest proof satisfies.

**This file closes that by identity, not by assertion.** It proves the AIR's reference object IS
`MinaWrapOpeningGate.openingResidual` — the same fold, cast into `ZMod p` — and then reads
`opening_relation_holds` (already proved, on Mina devnet block 539508, against values o1-labs'
own `SRS::verify` accepts) to conclude the forced predicate HOLDS at the real block.

So the checker theorem and the instance differential are welded into one object:

  * `openingCheck_forces` — a satisfying assignment ⟹ the residual is `O`. (The CHECK.)
  * `air_predicate_is_the_real_relation` — the residual the AIR forces IS the real block's
    `openingResidual`. (The WELD, this file.)
  * `opening_relation_holds` — that residual IS `O` on the real block. (The INSTANCE.)
  * and `MinaWrapOpeningGate`'s ten tamper poles say it is NOT `O` when any single input moves,
    so the forced predicate discriminates.

Together: the AIR does not refuse honest proofs, and it does not accept a proof with a moved
`z1`, `z2`, `c`, IPA challenge, aggregate, `sg`, `delta` or `u_base`.

## The one piece of real mathematics

`rcbAddM` (per-op reduced `Nat`, what the reality gate computes in) and `rcbAddZmod` (the
`ZMod p` formula, what the forcing lemmas conclude against) are DIFFERENT FUNCTIONS on different
types, and §1 proves the cast is a homomorphism between them. The delicate step is RCB's five
subtractions: `Nat` subtraction is truncated, so `rcbTraceM` computes `(x + p − y) % p`, and the
cast is only the field subtraction because every subtrahend in Algorithm 7 is itself the output
of a `% p`. That is checked, not assumed — `cast_Sb` carries `y < p` as a hypothesis and it is
discharged at each of the five sites by `Nat.mod_lt`.

Everything above that is `foldl_hom`: a fold of a homomorphism is the homomorphism of the fold.

## Axiom hygiene

`#assert_axioms`-clean; no `sorry`/`admit`/`native_decide`. NEW file; imports read-only. NOT
imported by the `Dregg2` root, per house practice for gates. Import line:
`import Dregg2.Circuit.Emit.MinaOpeningCheckWeld`
-/
import Dregg2.Circuit.Emit.PastaMsmAir
import Dregg2.Circuit.Emit.MinaWrapOpeningGate

namespace Dregg2.Circuit.Emit.MinaOpeningCheckWeld

open Dregg2.Circuit.Emit.PastaField (pN)
open Dregg2.Circuit.Emit.PastaCurveComplete (curveB3 rcbAddM rcbTraceM RcbT Oproj isInfM)
open Dregg2.Circuit.Emit.PastaScalarMul (PtP rcbAddZmod rcbOutG ladderM ladderRefFrom kDigits
  scMulLadderM)
open Dregg2.Circuit.Emit.PastaMsmAir (msmRefFrom openingResidualRef)
open Dregg2.Circuit.Emit.MinaWrapGroupGate (Pt padd msmComm smul)
open Dregg2.Circuit.Emit.MinaWrapOpeningGate (residualTerms openingResidual realResidual
  opening_relation_holds C Z1 Z2 CHAL CHAL_INV SG DELTA U_BASE)

set_option autoImplicit false
set_option maxRecDepth 20000000
set_option maxHeartbeats 4000000

/-! ## §1 — The cast is a homomorphism from the `Nat` RCB reference to the `ZMod p` one. -/

/-- A `Nat` projective point, read in `ZMod p`. -/
def castPt (P : Nat × Nat × Nat) : PtP :=
  ((P.1 : ZMod pN), (P.2.1 : ZMod pN), (P.2.2 : ZMod pN))

theorem pN_pos : 0 < pN := by decide +kernel

theorem cast_M (x y : Nat) : (((x * y) % pN : Nat) : ZMod pN) = (x : ZMod pN) * (y : ZMod pN) := by
  rw [ZMod.natCast_mod]; push_cast; ring

theorem cast_Ad (x y : Nat) : (((x + y) % pN : Nat) : ZMod pN) = (x : ZMod pN) + (y : ZMod pN) := by
  rw [ZMod.natCast_mod]; push_cast; ring

/-- ⚑ The truncated-subtraction step. `rcbTraceM` computes `(x + p − y) % p`; that is the field
difference exactly when `y < p`, which holds at all five RCB subtraction sites because every
subtrahend there is itself a `% p` output. The hypothesis is what makes this checked. -/
theorem cast_Sb (x y : Nat) (hy : y < pN) :
    (((x + pN - y) % pN : Nat) : ZMod pN) = (x : ZMod pN) - (y : ZMod pN) := by
  rw [ZMod.natCast_mod, Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self, add_zero]

/-- ⚑ **`rcbAddM_cast`** — the reality gate's `Nat` complete add and the forcing lemmas' `ZMod p`
complete add are THE SAME FUNCTION under the cast. Every rung above this is a fold of it. -/
theorem rcbAddM_cast (P Q : Nat × Nat × Nat) :
    castPt (rcbAddM pN curveB3 P Q) = rcbAddZmod (castPt P) (castPt Q) := by
  have hm : ∀ z : Nat, z % pN < pN := fun z => Nat.mod_lt _ pN_pos
  simp only [castPt, rcbAddM, rcbTraceM, RcbT.out, rcbAddZmod, rcbOutG, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> simp only [cast_Sb _ _ (hm _), cast_M, cast_Ad]

#assert_axioms cast_Sb
#assert_axioms rcbAddM_cast

/-! ## §2 — Folds: a fold of a homomorphism is the homomorphism of the fold, and a `List.range`
fold through `getD` is the list fold. Both generic; neither mentions Mina. -/

/-- **`foldl_hom`** — the transport that carries §1 up every level at once. -/
theorem foldl_hom {β γ ι : Type} (h : β → γ) (f : β → ι → β) (g : γ → ι → γ)
    (hstep : ∀ b i, h (f b i) = g (h b) i) :
    ∀ (l : List ι) (b : β), h (l.foldl f b) = l.foldl g (h b) := by
  intro l
  induction l with
  | nil => intro b; rfl
  | cons x xs ih => intro b; rw [List.foldl_cons, List.foldl_cons, ih, hstep]

/-- Indexing `List.range l.length` through `getD` reproduces the list. -/
theorem map_range_getD {α : Type} (l : List α) (d : α) :
    (List.range l.length).map (fun i => l.getD i d) = l := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-- …so a `List.range`-indexed fold IS the list fold. This is what lets the AIR's reference
(indexed by term number, because the emitted gates are) meet the reality gate's (a list fold). -/
theorem foldl_range_getD {α β : Type} (l : List α) (d : α) (g : β → α → β) (init : β) :
    (List.range l.length).foldl (fun acc i => g acc (l.getD i d)) init = l.foldl g init := by
  conv_rhs => rw [← map_range_getD l d]
  rw [List.foldl_map]

#assert_axioms foldl_hom
#assert_axioms map_range_getD
#assert_axioms foldl_range_getD

/-! ## §3 — The ladder: `PastaScalarMul.ladderM` (Nat, what `smul` runs) is `ladderRefFrom`
(`ZMod p`, what `pallasLadder_forces` concludes) under the cast. -/

/-- `castPt` commutes with the `(0,0,0)` default, so `getD` past the end agrees on both sides. -/
theorem castPt_zero : castPt (0, 0, 0) = ((0 : ZMod pN), (0 : ZMod pN), (0 : ZMod pN)) := by
  simp [castPt]

theorem getD_map_castPt (l : List (Nat × Nat × Nat)) (i : Nat) :
    (l.map castPt).getD i ((0 : ZMod pN), (0 : ZMod pN), (0 : ZMod pN))
      = castPt (l.getD i (0, 0, 0)) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : l[i]? with
  | none => simpa using castPt_zero.symm
  | some x => simp

/-- The Nat-side ladder as a `List.range` fold — the same shape `ladderRefFrom` has. -/
def ladderRefN (digits : List (Nat × Nat × Nat)) (n : Nat) (acc0 : Nat × Nat × Nat) :
    Nat × Nat × Nat :=
  (List.range n).foldl
    (fun acc i => rcbAddM pN curveB3 (rcbAddM pN curveB3 acc acc) (digits.getD i (0,0,0))) acc0

/-- …and at `n = |digits|` it IS `PastaScalarMul.ladderM`, the fold `smul` runs. -/
theorem ladderRefN_eq_ladderM (digits : List (Nat × Nat × Nat)) (acc0 : Nat × Nat × Nat) :
    ladderRefN digits digits.length acc0 = ladderM pN curveB3 digits acc0 :=
  foldl_range_getD digits (0,0,0)
    (fun acc d => rcbAddM pN curveB3 (rcbAddM pN curveB3 acc acc) d) acc0

/-- **`ladderRefFrom_cast`** — the `ZMod p` ladder the AIR forces is the cast of the `Nat` ladder
the reality gate computes. -/
theorem ladderRefFrom_cast (digits : List (Nat × Nat × Nat)) (n : Nat)
    (acc0 : Nat × Nat × Nat) :
    ladderRefFrom (digits.map castPt) n (castPt acc0) = castPt (ladderRefN digits n acc0) := by
  rw [ladderRefN, ladderRefFrom]
  refine (foldl_hom castPt
    (fun acc i => rcbAddM pN curveB3 (rcbAddM pN curveB3 acc acc) (digits.getD i (0,0,0)))
    (fun acc i => rcbAddZmod (rcbAddZmod acc acc)
      ((digits.map castPt).getD i ((0 : ZMod pN), (0 : ZMod pN), (0 : ZMod pN))))
    ?_ (List.range n) acc0).symm
  intro b i
  simp only [rcbAddM_cast, getD_map_castPt]

#assert_axioms ladderRefFrom_cast

/-! ## §4 — The MSM, and then the whole residual. -/

/-- `kDigits` emits exactly `nbits` digits. -/
theorem kDigits_length (k : Nat) (P : Nat × Nat × Nat) (nbits : Nat) :
    (kDigits k P nbits).length = nbits := by simp [kDigits]

/-- One MSM term's ladder IS `MinaWrapGroupGate.smul`, the 255-bit `[k]P` the reality gate runs. -/
theorem ladderRefN_255_eq_smul (k : Nat) (P : Pt) :
    ladderRefN (kDigits k P 255) 255 Oproj = smul k P := by
  have h := ladderRefN_eq_ladderM (kDigits k P 255) Oproj
  rw [kDigits_length] at h
  exact h

/-- The Nat-side MSM as a `List.range` fold over term indices. -/
def msmRefN (terms : List (Nat × Pt)) (nDigits n : Nat) (acc0 : Nat × Nat × Nat) :
    Nat × Nat × Nat :=
  (List.range n).foldl (fun acc i => rcbAddM pN curveB3 acc
    (ladderRefN (kDigits (terms.getD i (0, Oproj)).1 (terms.getD i (0, Oproj)).2 nDigits)
      nDigits Oproj)) acc0

/-- …and at `nDigits = 255`, `n = |terms|` it IS `MinaWrapGroupGate.msmComm`, the fold the real
block's opening residual is built from. -/
theorem msmRefN_eq_msmComm (terms : List (Nat × Pt)) :
    msmRefN terms 255 terms.length Oproj = msmComm terms := by
  rw [msmRefN, msmComm]
  have hf : (fun (acc : Nat × Nat × Nat) (i : Nat) => rcbAddM pN curveB3 acc
        (ladderRefN (kDigits (terms.getD i (0, Oproj)).1 (terms.getD i (0, Oproj)).2 255)
          255 Oproj))
      = (fun (acc : Nat × Nat × Nat) (i : Nat) =>
          (fun (a : Nat × Nat × Nat) (t : Nat × Pt) => padd a (smul t.1 t.2)) acc
            (terms.getD i (0, Oproj))) := by
    funext acc i; rw [ladderRefN_255_eq_smul]; rfl
  rw [hf]
  exact foldl_range_getD terms (0, Oproj) (fun acc t => padd acc (smul t.1 t.2)) Oproj

/-- **`msmRefFrom_cast`** — the AIR's reference MSM is the cast of the reality gate's. -/
theorem msmRefFrom_cast (terms : List (Nat × Pt)) (nDigits n : Nat) (acc0 : Nat × Nat × Nat)
    (dv : Nat → List PtP)
    (hdv : ∀ i, dv i = (kDigits (terms.getD i (0, Oproj)).1 (terms.getD i (0, Oproj)).2 nDigits
      ).map castPt) :
    msmRefFrom dv nDigits (castPt Oproj) n (castPt acc0)
      = castPt (msmRefN terms nDigits n acc0) := by
  rw [msmRefN, msmRefFrom]
  refine (foldl_hom castPt
    (fun acc i => rcbAddM pN curveB3 acc
      (ladderRefN (kDigits (terms.getD i (0, Oproj)).1 (terms.getD i (0, Oproj)).2 nDigits)
        nDigits Oproj))
    (fun acc i => rcbAddZmod acc (ladderRefFrom (dv i) nDigits (castPt Oproj)))
    ?_ (List.range n) acc0).symm
  intro b i
  simp only [rcbAddM_cast, hdv, ladderRefFrom_cast]

#assert_axioms kDigits_length
#assert_axioms ladderRefN_255_eq_smul
#assert_axioms msmRefN_eq_msmComm
#assert_axioms msmRefFrom_cast

/-! ## §5 — ⚑ THE WELD, at the real block. -/

/-- The digit bases' VALUES for the real block's 34-term opening residual: term `i` contributes
the 255 MSB-first digits of its scalar against its point, cast into `ZMod p`. This is the
`digitValsOf` argument `PastaMsmAir.openingCheck_forces` quantifies over. -/
def REAL_TERMS : List (Nat × Pt) :=
  residualTerms C Z1 Z2 CHAL CHAL_INV
    Dregg2.Circuit.Emit.MinaWrapAggregationGate.COMBINED_GOLD U_BASE SG

def realDigitVals (i : Nat) : List PtP :=
  (kDigits (REAL_TERMS.getD i (0, Oproj)).1 (REAL_TERMS.getD i (0, Oproj)).2 255).map castPt

/-- The real block's opening residual has **34 terms** — the count `PastaMsmAir` §5b prices. -/
theorem real_term_count : REAL_TERMS.length = 34 := by decide +kernel

/-- ⚑⚑ **`air_predicate_is_the_real_relation`** — **the object the emitted AIR forces IS the real
block's opening residual.** Not "agrees with", not "is checked against": the AIR's reference,
instantiated at the block's own 34 `(scalar, point)` terms and its `delta`, is `castPt` of
`MinaWrapOpeningGate.realResidual` — the very value `opening_relation_holds` evaluates. -/
theorem air_predicate_is_the_real_relation :
    openingResidualRef realDigitVals 255 (castPt Oproj) 34 (castPt Oproj) (castPt DELTA)
      = castPt realResidual := by
  have hmsm : msmRefFrom realDigitVals 255 (castPt Oproj) 34 (castPt Oproj)
      = castPt (msmComm REAL_TERMS) := by
    rw [show (34 : Nat) = REAL_TERMS.length from real_term_count.symm,
      msmRefFrom_cast REAL_TERMS 255 REAL_TERMS.length Oproj realDigitVals (fun _ => rfl),
      msmRefN_eq_msmComm]
  show rcbAddZmod (msmRefFrom realDigitVals 255 (castPt Oproj) 34 (castPt Oproj)) (castPt DELTA)
      = castPt (padd (msmComm REAL_TERMS) DELTA)
  rw [hmsm, show padd (msmComm REAL_TERMS) DELTA
      = rcbAddM pN curveB3 (msmComm REAL_TERMS) DELTA from rfl, rcbAddM_cast]

/-- `a % p = 0` reads as `a = 0` in `ZMod p`. -/
theorem cast_eq_zero_of_mod {a : Nat} (h : a % pN = 0) : ((a : Nat) : ZMod pN) = 0 := by
  rw [← ZMod.natCast_mod, h, Nat.cast_zero]

/-- ⚑⚑⚑ **`air_predicate_holds_on_the_real_block`** — **the predicate the emitted opening-check
AIR forces is SATISFIED by Mina devnet block 539508.**

This is the anti-vacuity floor of the whole file. `openingCheck_forces` would be equally provable
about a predicate no honest proof can meet — a forcing theorem true because its hypothesis is
unsatisfiable. It is not: the residual this AIR pins to the point at infinity is exactly the one
the real block's real IPA opening proof, at the challenges its own transcript samples, makes the
point at infinity. Read together with `MinaWrapOpeningGate`'s ten tamper poles — each of which
moves one input and takes the residual off `O` — the forced predicate both ACCEPTS the honest
object and REJECTS the tampered ones. -/
theorem air_predicate_holds_on_the_real_block :
    (openingResidualRef realDigitVals 255 (castPt Oproj) 34 (castPt Oproj) (castPt DELTA)).1 = 0
    ∧ (openingResidualRef realDigitVals 255 (castPt Oproj) 34 (castPt Oproj)
        (castPt DELTA)).2.2 = 0 := by
  have hinf := opening_relation_holds
  rw [isInfM, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hinf
  rw [air_predicate_is_the_real_relation]
  exact ⟨cast_eq_zero_of_mod hinf.2, cast_eq_zero_of_mod hinf.1⟩

#assert_axioms air_predicate_is_the_real_relation
#assert_axioms air_predicate_holds_on_the_real_block

/-! ## §6 — What the weld does and does NOT buy.

**Buys.** The forced predicate is pinned to the object o1-labs' own `SRS::verify` accepts, by
IDENTITY rather than by two computations agreeing. `PastaMsmAir.openingCheck_forces` can no
longer be a true theorem about the wrong equation, and cannot be vacuously true — §5 exhibits a
real satisfying value for its conclusion.

**Does not buy.**

  * **It is not a satisfying ASSIGNMENT.** §5 says the reference residual is `O` at the real
    block; it does not materialise the 573,377-gate witness (every RCB intermediate, quotient and
    carry column) that would make `acceptB` return `true`. That is the PROVER's job and the
    subject of the witness-generation perimeter, not the kernel's. The gap is named, and the
    terminal gadget's own satisfiability — the one genuinely new gate here — IS exhibited, in
    `PastaMsmAir` §3b.
  * **P10 is untouched**, exactly as in `PastaMsmAir` §6.1. The relation HOLDING is not the
    prover KNOWING an opening.
  * **The `⟨s, srs.g⟩` leg is not welded**, because its AIR is not emitted (`PastaMsmAir` §6.2).
    Statement (B) here uses `sg` as supplied; that it is `⟨s, srs.g⟩` is rung 5h's `decide`, an
    instance fact about one block, and the checker theorem for it is the named gap.
  * **RCB completeness is still inherited** (RCB'15 Thm 1). §1 proves the two RCB *formulas*
    agree under the cast; that the formula is the group law is the shared residual.
-/

end Dregg2.Circuit.Emit.MinaOpeningCheckWeld

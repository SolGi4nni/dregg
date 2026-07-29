/-
# Dregg2.Circuit.Emit.PastaMsmLayouts — **the two named gaps of `PastaMsmAir`, closed and priced.**

Lean-authored AIR: `def`-generators producing `List VmConstraint2` plus forcing lemmas over the
ACTUALLY EMITTED list. Rust hand-writes no constraint, no builder gadget, no `air_accepts` here.

`PastaMsmAir` (commit `6c94fceea`) turned the Mina IPA opening check into a theorem about the
CHECKER — `openingCheck_forces`, gate-count-independent — and then named two gaps precisely:

  * **the Horner / bit-plane AIR is not emitted**, and the cheap `4.16M` figure is a SET-BIT count
    that needs "a skip argument nothing here builds";
  * **GLV is unbuilt**, so `nDigits = 255` is a ceiling.

This file closes both, and the closing changes the answer.

## §A — the skip argument does not exist, and that is a THEOREM, not a shrug

`msmGatesFrom : (Nat → List (Nat × Nat × Nat)) → Nat → … → List VmConstraint2` has no `Assignment`
in its type, and `horner_layout_is_witness_independent` (§3) proves the consequence: **the emitted
gate count is a function of `(n, nbits)` alone.** No choice of bit columns, digit columns or point
columns moves it. So the `4,161,791` set-bit count is not the height of any trace this vocabulary
can emit; the emitted bit-plane height is `nbits·(n+1) = 8,356,095`, which is `2.008×` it. **The
Horner win over term-by-term is 2×, not 4×** (`horner_beats_ladder_by_two`, and the ratio guard
that pins it below 4×). That is the honest version of the gap, and it is the first correction.

## §B — the selector is the only "if" a circuit gets, and it is cheap

§1 emits `condPointGates` — a bit pin plus one linear-select per coordinate, **4 core gates and 28
columns** — forcing `D = if b then P else O` where `O = (0 : 1 : 0)` is RCB's point at infinity.
It needs NO quotient witness: `b ∈ {0,1}` makes `b·X` exact over ℤ, so the gate is an identity, not
a congruence. §4's `glvDigitGates` is the same idea at a 4-entry table: **6 core gates, 30 columns**,
against `RCB_GATES = 33` for the add it feeds. The selector is not the cost.

Both are exhibited SATISFIABLE at every selection and REFUTABLE at a forged one (§1b, §4b), because
a forcing theorem whose hypothesis nothing satisfies is true and worthless.

## §C — GLV is built, it is sound, and it is 2× on statement (B) — and a WASH on (A)

§4 forces the digit to be the `{O, P, φP, P+φP}` table entry the two witness bits select, and §5
binds the halves: one gate for `k₁ + λ·k₂ ≡ k (mod q)` (`λ` is a CONSTANT, so it is degree 1) and
one gate per half for the MSB-first bit recomposition. Together these close `PastaMsmAir` §6.6 —
"the digits are represented inputs, not derived" — which is a SOUNDNESS gain, not only a speed one:
before this, nothing in the emitted AIR said the ladder's digits were the bits of the scalar.

⚑ **The lattice result transfers, but not the way it reads.** `PicklesTranscriptBinding`'s
`glvA/glvB` are the reduced basis of `{(x,y) : x ≡ y·lambdaVesta (mod pN)}` — **Vesta's** lattice.
This AIR is **Pallas** (`pallasCompleteAdd`, base field `pN`), so its scalars live mod `qN` and its
lambda is `lambdaPallas`. §5b Gauss-reduces THAT lattice and `decide`-checks the same three
certificates. And the `2^70` minimality bound does NOT transfer and is NOT needed: at 128-bit halves
the decomposition is not unique (`2^256/qN ≈ 2^1.5` representations), and soundness never wanted
uniqueness — every representation multiplies to the same point. **The lattice is a COMPLETENESS
certificate here, not a soundness one.** Said out loud because the opposite reading is the natural one.

⚑ **And GLV does not help statement (A) the way it helps (B)** (§6). GLV halves the SERIAL doubling
depth. The bit-plane scan has already amortised that depth to nothing — one doubling per plane,
shared by all `n` terms. Treating `φP` as an extra term would DOUBLE `n` to halve `nbits`: a wash,
and slightly worse. The 4-entry table recovers the win (`nbits` halves, `n` does not), and lands at
`4,227,200` rows — `2.016×` the two-adicity ceiling. Which is the second correction, and the one
that decides the question.

## §D — what the numbers say

Against the deployed geometry (`log_blowup = 6`, `BabyBear::TWO_ADICITY = 27` ⟹ **`2^21` trace rows,
a p3 panic, not a repo check**; `WRAP_LOG_CEIL = 16` ⟹ a `2^16` root segment; `F ≈ 0.094 ms` per row
for the FRI fold):

  * **statement (B), 34 terms** — `17,375 → 8,773` RCB adds (`1.98×`), `573,377 → 315,691` core
    gates. **13.4% of one root segment**, from 26.5%. GLV is worth building for (B) and it is built.
  * **statement (A), 32,768 terms** — every emitted layout, priced as a theorem:

    | layout | rows | ÷ `2^21` | root segments | FRI floor |
    |---|---|---|---|---|
    | term-by-term ladder, 255 | 16,744,449 | 7.98× | 256 | 26 min |
    | bit-plane Horner, 255 | 8,356,095 | 3.98× | 128 | 13 min |
    | bit-plane + GLV table, 128 | 4,227,200 | 2.016× | 65 | 6.6 min |
    | …with public `P+φP` | 4,194,432 | 2.0001× | 65 | 6.6 min |
    | (the set-bit count — UNREACHABLE) | 4,161,791 | — | — | — |

    **The best emitted layout misses the hard ceiling by a factor of 2.** It misses `2^22` — the
    ceiling one blowup step down — by **128 rows, exactly the 128 doublings.** That is not a
    coincidence to optimise away: `2^21` is a property of BabyBear's two-adicity, not of the prover,
    so no better algorithm inside this vocabulary reaches it. Going to `log_blowup = 5` would, and
    that WEAKENS a rate; it is not ours to take.

**So: (A) does not fit one dregg proof, and the recommendation is to defer it exactly as Pickles
does** (`PastaIPA.sVec_eq_bPoly` — `k = 15` challenges determine all `2^15` scalars). See §7.

## Axiom hygiene

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`/`admit`/
`native_decide`. `#guard` KATs reduce in the kernel. Imports read-only (`PastaMsmAir`,
transitively `PastaScalarMul`/`PastaCurveComplete`/`PastaCurve`/`PastaField`/`AirBuilder`). NEW
file; NOT imported by the `Dregg2` root, per house practice for gates. Import line:
`import Dregg2.Circuit.Emit.PastaMsmLayouts`
-/
import Dregg2.Circuit.Emit.PastaMsmAir

namespace Dregg2.Circuit.Emit.PastaMsmLayouts

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.DescriptorIR2 (VmConstraint2 EffectVmDescriptor2)
open Dregg2.Circuit.Emit.AirBuilder
open Dregg2.Circuit.Emit.Bls12381Tower (evalH_mul)
open Dregg2.Circuit.Emit.PastaField (pN qN fpValue fpVal fpVal_eq gateBodyEvalZero acceptB
  bumpAt)
open Dregg2.Circuit.Emit.PastaCurve (lambdaPallas)
open Dregg2.Circuit.Emit.PastaCurveComplete (pallasCompleteAdd)
open Dregg2.Circuit.Emit.PastaScalarMul (PtP PointIsZ rcbAddZmod pallasRcbStep_forces
  acceptB_append acceptB_prefix acceptB_suffix gateBodyEvalZero_cgH)
open Dregg2.Circuit.Emit.PastaMsmAir (RCB_GATES RCB_COLS pallasCompleteAdd_length
  pallasCompleteAdd_fresh openingCheckRcbAdds openingCheckGateCount openingCheckColCount
  DREGG_ROOT_ROWS DREGG_MAX_ROWS DREGG_MAX_WIDTH)

set_option autoImplicit false
set_option maxRecDepth 8000

/-! ## §0 — Two one-line bridges the sibling files did not need. -/

/-- A raw-expression gate's body reading (the `cgH` analogue for `binGate`). -/
theorem gateBodyEvalZero_cg (a : Assignment) (e : EmittedExpr) :
    gateBodyEvalZero a (cg e) = decide (e.eval a = 0) := rfl

/-- The boolean pin, read off `acceptB`. -/
theorem binGate_forces (a : Assignment) (co : Nat)
    (h : gateBodyEvalZero a (binGate co) = true) : a co = 0 ∨ a co = 1 := by
  rw [binGate, gateBodyEvalZero_cg] at h
  exact (gBin_eval_zero_iff a co).mp (of_decide_eq_true h)

/-! ## §1 — THE SELECTOR: the only way an AIR gets to say "if".

`condPointGates b P D` forces `D = P` when the witness bit `b` is 1 and `D = O = (0 : 1 : 0)` when
it is 0. Three linear-select gates plus the bit pin. **No quotient witness anywhere**: `b ∈ {0,1}`
makes `b·X` exact over ℤ, so each gate is an IDENTITY on the reconstructed values, not a congruence
— which is why the selector costs 4 gates against the 33 of the add it feeds. -/

/-- `b·(value at `src`) − (value at `dst`)` — the select whose zero branch is `0`. -/
def selZeroHead (bCol src dst : Nat) : Head :=
  ((Head.lin 1 bCol).mul (fpValue src)).append ((fpValue dst).scale (-1))

/-- `b·(value at `src`) + (1 − b) − (value at `dst`)` — the select whose zero branch is `1`
(the `Y` coordinate of `O`). -/
def selOneHead (bCol src dst : Nat) : Head :=
  ((((Head.lin 1 bCol).mul (fpValue src)).addLin (-1) bCol).addConst 1).append
    ((fpValue dst).scale (-1))

theorem selZeroHead_eval (a : Assignment) (bCol src dst : Nat) :
    evalH (selZeroHead bCol src dst) a = a bCol * fpVal a src - fpVal a dst := by
  simp only [selZeroHead, evalH_append, evalH_scale, evalH_mul, evalH_lin, fpVal_eq]; ring

theorem selOneHead_eval (a : Assignment) (bCol src dst : Nat) :
    evalH (selOneHead bCol src dst) a
      = a bCol * fpVal a src - a bCol + 1 - fpVal a dst := by
  simp only [selOneHead, evalH_append, evalH_scale, evalH_addConst, evalH_addLin, evalH_mul,
    evalH_lin, fpVal_eq]
  ring

/-- The reference the selector forces: `if bit then P else O`. In RCB's projective model the point
at infinity is `(0 : 1 : 0)` — `PastaCurveComplete.Oproj`, read in `ZMod p`. -/
def condRef (bit : Bool) (P : PtP) : PtP := if bit then P else (0, 1, 0)

/-- **`condPointGates`** — the conditional-add digit: `4` core gates. -/
def condPointGates (bCol pX pY pZ dX dY dZ : Nat) : List VmConstraint2 :=
  [ binGate bCol
  , cgH (selZeroHead bCol pX dX)
  , cgH (selOneHead bCol pY dY)
  , cgH (selZeroHead bCol pZ dZ) ]

/-- The bit the assignment actually carries at a selector column. -/
def bitAt (a : Assignment) (bCol : Nat) : Bool := decide (a bCol = 1)

/-- ⚑ **`condPoint_forces`** — the emitted selector FORCES the digit columns to represent exactly
`if b then P else O`, at the bit the assignment carries. No existential: the reference reads the
witness column, so the conclusion is about the assignment in front of us. -/
theorem condPoint_forces (a : Assignment) (bCol pX pY pZ dX dY dZ : Nat) {P : PtP}
    (hP : PointIsZ a pX pY pZ P)
    (hacc : acceptB (condPointGates bCol pX pY pZ dX dY dZ) a = true) :
    PointIsZ a dX dY dZ (condRef (bitAt a bCol) P) := by
  simp only [condPointGates, acceptB, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true, gateBodyEvalZero_cgH] at hacc
  obtain ⟨hb, gX, gY, gZ⟩ := hacc
  have hX : a bCol * fpVal a pX - fpVal a dX = 0 := by
    have h := of_decide_eq_true gX; rwa [selZeroHead_eval] at h
  have hY : a bCol * fpVal a pY - a bCol + 1 - fpVal a dY = 0 := by
    have h := of_decide_eq_true gY; rwa [selOneHead_eval] at h
  have hZ : a bCol * fpVal a pZ - fpVal a dZ = 0 := by
    have h := of_decide_eq_true gZ; rwa [selZeroHead_eval] at h
  obtain ⟨hPx, hPy, hPz⟩ := hP
  rcases binGate_forces a bCol hb with h0 | h1
  · -- the bit is 0: the digit is the point at infinity
    have hbit : bitAt a bCol = false := by simp [bitAt, h0]
    rw [h0] at hX hY hZ
    refine ⟨?_, ?_, ?_⟩ <;> simp only [hbit, condRef]
    · rw [show fpVal a dX = 0 by linarith]; simp
    · rw [show fpVal a dY = 1 by linarith]; simp
    · rw [show fpVal a dZ = 0 by linarith]; simp
  · -- the bit is 1: the digit IS the point
    have hbit : bitAt a bCol = true := by simp [bitAt, h1]
    rw [h1] at hX hY hZ
    refine ⟨?_, ?_, ?_⟩ <;> simp only [hbit, condRef, if_true]
    · rw [show fpVal a dX = fpVal a pX by linarith]; exact hPx
    · rw [show fpVal a dY = fpVal a pY by linarith]; exact hPy
    · rw [show fpVal a dZ = fpVal a pZ by linarith]; exact hPz

#assert_axioms selZeroHead_eval
#assert_axioms selOneHead_eval
#assert_axioms condPoint_forces

/-! ### §1b — the selector BITES: satisfiable at BOTH selections, refutable at a forged one.

`AirBuilder.rangeNonneg` sat in this tree for months as a shape every consumer read as a check.
These `#guard`s are that instrument applied at birth. The third block is the one that matters: a
prover who sets the bit to 0 and still supplies `P` as the digit — i.e. adds a term it did not pay
for — is REFUSED. -/

open Dregg2.Circuit.Emit.PastaField.Ref (limbOf X Y)

/-- Layout: bit at col 0, `P = (X,Y,Z)` at 1/10/19, digit at 28/37/46. -/
def condAsg (bit : Bool) (Xv Yv Zv : Nat) : Assignment := fun col =>
  if col = 0 then (if bit then 1 else 0)
  else if col < 10 then limbOf Xv (col - 1)
  else if col < 19 then limbOf Yv (col - 10)
  else if col < 28 then limbOf Zv (col - 19)
  else if col < 37 then limbOf (if bit then Xv else 0) (col - 28)
  else if col < 46 then limbOf (if bit then Yv else 1) (col - 37)
  else if col < 55 then limbOf (if bit then Zv else 0) (col - 46)
  else 0

/-- The FORGED assignment: bit 0, but the digit is `P` anyway. -/
def condForge (Xv Yv Zv : Nat) : Assignment := fun col =>
  if col = 0 then 0
  else if col < 10 then limbOf Xv (col - 1)
  else if col < 19 then limbOf Yv (col - 10)
  else if col < 28 then limbOf Zv (col - 19)
  else if col < 37 then limbOf Xv (col - 28)
  else if col < 46 then limbOf Yv (col - 37)
  else if col < 55 then limbOf Zv (col - 46)
  else 0

def condGates : List VmConstraint2 := condPointGates 0 1 10 19 28 37 46

-- SATISFIABLE at both selections (so `condPoint_forces` is not true-because-empty) …
#guard acceptB condGates (condAsg true X Y 1) == true
#guard acceptB condGates (condAsg false X Y 1) == true
-- … and at a non-canonical point (the congruence chain never asked for canonical limbs).
#guard acceptB condGates (condAsg true (X + pN) Y 1) == true
-- REFUTABLE: the bit says "skip" and the digit says "add" — the free-term forgery, REFUSED.
#guard acceptB condGates (condForge X Y 1) == false
-- REFUTABLE: bit 1 and a bumped digit limb.
#guard acceptB condGates (bumpAt (condAsg true X Y 1) 28) == false
#guard acceptB condGates (bumpAt (condAsg false X Y 1) 37) == false
-- REFUTABLE: the bit itself is not a bit.
#guard acceptB condGates (bumpAt (condAsg true X Y 1) 0) == false

/-! ## §2 — THE BIT-PLANE (HORNER) AIR, emitted.

One shared doubling chain: at each of `nbits` planes, double the accumulator once, then fold ONE
conditional add per term. `PastaIpaFold.msmHorner_eq_msmN` is the identity this realises; what is
new here is the CIRCUIT and its forcing.

Column discipline is `PastaMsmAir`'s: the caller supplies the bit column (`bitOf`), the digit point
columns (`digOf`) and the fixed base-point columns (`ptsOf`) as layout FUNCTIONS, exactly as
`msmGatesFrom` takes `digitsOf`; only the RCB intermediates thread. -/

/-- One `(plane, term)` conditional accumulate: select `bᵢ·Pᵢ`, then one RCB complete add. -/
def hornerAddStep (ptsOf : Nat → Nat × Nat × Nat) (bitOf : Nat → Nat)
    (digOf : Nat → Nat × Nat × Nat) :
    List VmConstraint2 × (Nat × Nat × Nat) × Nat → Nat →
    List VmConstraint2 × (Nat × Nat × Nat) × Nat :=
  fun st i =>
    let sel := condPointGates (bitOf i) (ptsOf i).1 (ptsOf i).2.1 (ptsOf i).2.2
                 (digOf i).1 (digOf i).2.1 (digOf i).2.2
    let add := pallasCompleteAdd st.2.1.1 st.2.1.2.1 st.2.1.2.2
                 (digOf i).1 (digOf i).2.1 (digOf i).2.2 st.2.2
    (st.1 ++ (sel ++ add.1), add.2.1, add.2.2)

/-- One bit plane: ONE doubling (shared by every term — the whole point), then `n` conditional
adds. -/
def hornerPlaneStep (ptsOf : Nat → Nat × Nat × Nat) (bitOf : Nat → Nat → Nat)
    (digOf : Nat → Nat → Nat × Nat × Nat) (n : Nat) :
    List VmConstraint2 × (Nat × Nat × Nat) × Nat → Nat →
    List VmConstraint2 × (Nat × Nat × Nat) × Nat :=
  fun st plane =>
    let dbl := pallasCompleteAdd st.2.1.1 st.2.1.2.1 st.2.1.2.2
                 st.2.1.1 st.2.1.2.1 st.2.1.2.2 st.2.2
    let inner := (List.range n).foldl (hornerAddStep ptsOf (bitOf plane) (digOf plane))
                   ([], dbl.2.1, dbl.2.2)
    (st.1 ++ (dbl.1 ++ inner.1), inner.2.1, inner.2.2)

/-- **The emitted bit-plane MSM.** `n` (terms) and `nbits` (planes) are parameters, not literals. -/
def hornerGatesFrom (ptsOf : Nat → Nat × Nat × Nat) (bitOf : Nat → Nat → Nat)
    (digOf : Nat → Nat → Nat × Nat × Nat) (n nbits : Nat) (acc0 : Nat × Nat × Nat)
    (fresh0 : Nat) : List VmConstraint2 × (Nat × Nat × Nat) × Nat :=
  (List.range nbits).foldl (hornerPlaneStep ptsOf bitOf digOf n) ([], acc0, fresh0)

/-- The reference one plane computes: double, then accumulate the selected digits. -/
def hornerPlaneRef (ptVals : Nat → PtP) (bits : Nat → Nat → Bool) (n : Nat) :
    PtP → Nat → PtP :=
  fun acc plane =>
    (List.range n).foldl (fun b i => rcbAddZmod b (condRef (bits plane i) (ptVals i)))
      (rcbAddZmod acc acc)

/-- The reference the whole scan computes. -/
def hornerRefFrom (ptVals : Nat → PtP) (bits : Nat → Nat → Bool) (n nbits : Nat) (acc0 : PtP) :
    PtP :=
  (List.range nbits).foldl (hornerPlaneRef ptVals bits n) acc0

/-! ### §2a — the two prefix lemmas (`PastaScalarMul.dstep_prefix`'s shape, twice). -/

theorem hornerAddStep_prefix (ptsOf : Nat → Nat × Nat × Nat) (bitOf : Nat → Nat)
    (digOf : Nat → Nat × Nat × Nat) : ∀ (ts : List Nat)
    (Xs : List VmConstraint2) (acc : Nat × Nat × Nat) (fr : Nat),
    ∃ Ys, (ts.foldl (hornerAddStep ptsOf bitOf digOf) (Xs, acc, fr)).1 = Xs ++ Ys := by
  intro ts
  induction ts with
  | nil => intro Xs acc fr; exact ⟨[], by simp⟩
  | cons t rest ih =>
    intro Xs acc fr
    rw [List.foldl_cons]
    obtain ⟨Ys, hY⟩ := ih (hornerAddStep ptsOf bitOf digOf (Xs, acc, fr) t).1
      (hornerAddStep ptsOf bitOf digOf (Xs, acc, fr) t).2.1
      (hornerAddStep ptsOf bitOf digOf (Xs, acc, fr) t).2.2
    refine ⟨(condPointGates (bitOf t) (ptsOf t).1 (ptsOf t).2.1 (ptsOf t).2.2
              (digOf t).1 (digOf t).2.1 (digOf t).2.2
             ++ (pallasCompleteAdd acc.1 acc.2.1 acc.2.2
                  (digOf t).1 (digOf t).2.1 (digOf t).2.2 fr).1) ++ Ys, ?_⟩
    rw [show (hornerAddStep ptsOf bitOf digOf (Xs, acc, fr) t)
        = ((hornerAddStep ptsOf bitOf digOf (Xs, acc, fr) t).1,
           (hornerAddStep ptsOf bitOf digOf (Xs, acc, fr) t).2.1,
           (hornerAddStep ptsOf bitOf digOf (Xs, acc, fr) t).2.2) from rfl] at hY
    rw [hY]; dsimp only [hornerAddStep]; rw [List.append_assoc]

theorem hornerPlaneStep_prefix (ptsOf : Nat → Nat × Nat × Nat) (bitOf : Nat → Nat → Nat)
    (digOf : Nat → Nat → Nat × Nat × Nat) (n : Nat) : ∀ (ts : List Nat)
    (Xs : List VmConstraint2) (acc : Nat × Nat × Nat) (fr : Nat),
    ∃ Ys, (ts.foldl (hornerPlaneStep ptsOf bitOf digOf n) (Xs, acc, fr)).1 = Xs ++ Ys := by
  intro ts
  induction ts with
  | nil => intro Xs acc fr; exact ⟨[], by simp⟩
  | cons t rest ih =>
    intro Xs acc fr
    rw [List.foldl_cons]
    obtain ⟨Ys, hY⟩ := ih (hornerPlaneStep ptsOf bitOf digOf n (Xs, acc, fr) t).1
      (hornerPlaneStep ptsOf bitOf digOf n (Xs, acc, fr) t).2.1
      (hornerPlaneStep ptsOf bitOf digOf n (Xs, acc, fr) t).2.2
    refine ⟨((pallasCompleteAdd acc.1 acc.2.1 acc.2.2 acc.1 acc.2.1 acc.2.2 fr).1
             ++ ((List.range n).foldl (hornerAddStep ptsOf (bitOf t) (digOf t))
                  ([], (pallasCompleteAdd acc.1 acc.2.1 acc.2.2 acc.1 acc.2.1 acc.2.2 fr).2.1,
                       (pallasCompleteAdd acc.1 acc.2.1 acc.2.2 acc.1 acc.2.1 acc.2.2 fr).2.2)).1)
            ++ Ys, ?_⟩
    rw [show (hornerPlaneStep ptsOf bitOf digOf n (Xs, acc, fr) t)
        = ((hornerPlaneStep ptsOf bitOf digOf n (Xs, acc, fr) t).1,
           (hornerPlaneStep ptsOf bitOf digOf n (Xs, acc, fr) t).2.1,
           (hornerPlaneStep ptsOf bitOf digOf n (Xs, acc, fr) t).2.2) from rfl] at hY
    rw [hY]; dsimp only [hornerPlaneStep]; rw [List.append_assoc]

/-! ### §2b — THE FORCING, independent of BOTH `n` and `nbits`.

Two `List.range` inductions, one nested in the other. Neither mentions a gate count, a term count
or a plane count except as a fold bound: the statement at `n = 32768, nbits = 255` is the same
theorem as the statement at `n = 1, nbits = 1`. -/

/-- The inner fold — one plane's `n` conditional adds. -/
theorem foldl_hornerAddStep_forces (a : Assignment) (ptsOf : Nat → Nat × Nat × Nat)
    (bitOf : Nat → Nat) (digOf : Nat → Nat × Nat × Nat) (ptVals : Nat → PtP) :
    ∀ (ts : List Nat) (cs0 : List VmConstraint2) (acc0 : Nat × Nat × Nat) (fr0 : Nat) (av0 : PtP),
      PointIsZ a acc0.1 acc0.2.1 acc0.2.2 av0 →
      (∀ i ∈ ts, PointIsZ a (ptsOf i).1 (ptsOf i).2.1 (ptsOf i).2.2 (ptVals i)) →
      acceptB ((ts.foldl (hornerAddStep ptsOf bitOf digOf) (cs0, acc0, fr0)).1) a = true →
      PointIsZ a (ts.foldl (hornerAddStep ptsOf bitOf digOf) (cs0, acc0, fr0)).2.1.1
        (ts.foldl (hornerAddStep ptsOf bitOf digOf) (cs0, acc0, fr0)).2.1.2.1
        (ts.foldl (hornerAddStep ptsOf bitOf digOf) (cs0, acc0, fr0)).2.1.2.2
        (ts.foldl (fun b i => rcbAddZmod b (condRef (bitAt a (bitOf i)) (ptVals i))) av0) := by
  intro ts
  induction ts with
  | nil => intro cs0 acc0 fr0 av0 hav0 _ _; exact hav0
  | cons t rest ih =>
    intro cs0 acc0 fr0 av0 hav0 hP hacc
    rw [List.foldl_cons] at hacc ⊢
    rw [List.foldl_cons]
    set sel := condPointGates (bitOf t) (ptsOf t).1 (ptsOf t).2.1 (ptsOf t).2.2
                 (digOf t).1 (digOf t).2.1 (digOf t).2.2 with hsel
    set add := pallasCompleteAdd acc0.1 acc0.2.1 acc0.2.2
                 (digOf t).1 (digOf t).2.1 (digOf t).2.2 fr0 with hadd
    have hstep : hornerAddStep ptsOf bitOf digOf (cs0, acc0, fr0) t
        = (cs0 ++ (sel ++ add.1), add.2.1, add.2.2) := rfl
    rw [hstep] at hacc ⊢
    obtain ⟨Ys, hY⟩ := hornerAddStep_prefix ptsOf bitOf digOf rest (cs0 ++ (sel ++ add.1)) _ _
    have haccStep : acceptB (sel ++ add.1) a = true := by
      have h1 : acceptB (cs0 ++ (sel ++ add.1)) a = true :=
        acceptB_prefix (cs0 ++ (sel ++ add.1)) Ys a (by rw [hY] at hacc; exact hacc)
      exact acceptB_suffix cs0 (sel ++ add.1) a h1
    have haccSel : acceptB sel a = true := acceptB_prefix _ _ a haccStep
    have haccAdd : acceptB add.1 a = true := acceptB_suffix _ _ a haccStep
    have hdig : PointIsZ a (digOf t).1 (digOf t).2.1 (digOf t).2.2
        (condRef (bitAt a (bitOf t)) (ptVals t)) :=
      condPoint_forces a (bitOf t) (ptsOf t).1 (ptsOf t).2.1 (ptsOf t).2.2
        (digOf t).1 (digOf t).2.1 (digOf t).2.2 (hP t List.mem_cons_self) haccSel
    have hnext : PointIsZ a add.2.1.1 add.2.1.2.1 add.2.1.2.2
        (rcbAddZmod av0 (condRef (bitAt a (bitOf t)) (ptVals t))) :=
      pallasRcbStep_forces a acc0.1 acc0.2.1 acc0.2.2
        (digOf t).1 (digOf t).2.1 (digOf t).2.2 fr0 hav0 hdig haccAdd
    exact ih (cs0 ++ (sel ++ add.1)) _ _ _ hnext
      (fun i hi => hP i (List.mem_cons_of_mem t hi)) hacc

/-- The outer fold — the `nbits` planes. -/
theorem foldl_hornerPlaneStep_forces (a : Assignment) (ptsOf : Nat → Nat × Nat × Nat)
    (bitOf : Nat → Nat → Nat) (digOf : Nat → Nat → Nat × Nat × Nat) (n : Nat)
    (ptVals : Nat → PtP)
    (hP : ∀ i < n, PointIsZ a (ptsOf i).1 (ptsOf i).2.1 (ptsOf i).2.2 (ptVals i)) :
    ∀ (ts : List Nat) (cs0 : List VmConstraint2) (acc0 : Nat × Nat × Nat) (fr0 : Nat) (av0 : PtP),
      PointIsZ a acc0.1 acc0.2.1 acc0.2.2 av0 →
      acceptB ((ts.foldl (hornerPlaneStep ptsOf bitOf digOf n) (cs0, acc0, fr0)).1) a = true →
      PointIsZ a (ts.foldl (hornerPlaneStep ptsOf bitOf digOf n) (cs0, acc0, fr0)).2.1.1
        (ts.foldl (hornerPlaneStep ptsOf bitOf digOf n) (cs0, acc0, fr0)).2.1.2.1
        (ts.foldl (hornerPlaneStep ptsOf bitOf digOf n) (cs0, acc0, fr0)).2.1.2.2
        (ts.foldl (hornerPlaneRef ptVals (fun pl i => bitAt a (bitOf pl i)) n) av0) := by
  intro ts
  induction ts with
  | nil => intro cs0 acc0 fr0 av0 hav0 _; exact hav0
  | cons t rest ih =>
    intro cs0 acc0 fr0 av0 hav0 hacc
    rw [List.foldl_cons] at hacc ⊢
    rw [List.foldl_cons]
    set dbl := pallasCompleteAdd acc0.1 acc0.2.1 acc0.2.2 acc0.1 acc0.2.1 acc0.2.2 fr0 with hdbl
    set inner := (List.range n).foldl (hornerAddStep ptsOf (bitOf t) (digOf t))
                   ([], dbl.2.1, dbl.2.2) with hinner
    have hstep : hornerPlaneStep ptsOf bitOf digOf n (cs0, acc0, fr0) t
        = (cs0 ++ (dbl.1 ++ inner.1), inner.2.1, inner.2.2) := rfl
    rw [hstep] at hacc ⊢
    obtain ⟨Ys, hY⟩ := hornerPlaneStep_prefix ptsOf bitOf digOf n rest
      (cs0 ++ (dbl.1 ++ inner.1)) _ _
    have haccStep : acceptB (dbl.1 ++ inner.1) a = true := by
      have h1 : acceptB (cs0 ++ (dbl.1 ++ inner.1)) a = true :=
        acceptB_prefix (cs0 ++ (dbl.1 ++ inner.1)) Ys a (by rw [hY] at hacc; exact hacc)
      exact acceptB_suffix cs0 (dbl.1 ++ inner.1) a h1
    have haccDbl : acceptB dbl.1 a = true := acceptB_prefix _ _ a haccStep
    have haccInner : acceptB inner.1 a = true := acceptB_suffix _ _ a haccStep
    have hd : PointIsZ a dbl.2.1.1 dbl.2.1.2.1 dbl.2.1.2.2 (rcbAddZmod av0 av0) :=
      pallasRcbStep_forces a acc0.1 acc0.2.1 acc0.2.2 acc0.1 acc0.2.1 acc0.2.2 fr0
        hav0 hav0 haccDbl
    have hin := foldl_hornerAddStep_forces a ptsOf (bitOf t) (digOf t) ptVals
      (List.range n) [] dbl.2.1 dbl.2.2 (rcbAddZmod av0 av0) hd
      (fun i hi => hP i (List.mem_range.mp hi)) haccInner
    exact ih (cs0 ++ (dbl.1 ++ inner.1)) _ _ _ hin hacc

/-- ⚑⚑ **`hornerGates_forces`** — **the emitted bit-plane AIR forces the bit-plane scan.** Any
assignment satisfying the generated constraints has its accumulator columns representing, in
`ZMod p`, the Horner scan of the represented base points against the bits the assignment itself
carries in its selector columns.

`n` and `nbits` are universally quantified and appear NOWHERE in the proof except as fold bounds —
`pallasLadder_forces`'s discipline, one level up and in the other direction. -/
theorem hornerGates_forces (a : Assignment) (ptsOf : Nat → Nat × Nat × Nat)
    (bitOf : Nat → Nat → Nat) (digOf : Nat → Nat → Nat × Nat × Nat) (ptVals : Nat → PtP)
    (n nbits : Nat) (acc0 : Nat × Nat × Nat) (fresh0 : Nat) (av0 : PtP)
    (hav0 : PointIsZ a acc0.1 acc0.2.1 acc0.2.2 av0)
    (hP : ∀ i < n, PointIsZ a (ptsOf i).1 (ptsOf i).2.1 (ptsOf i).2.2 (ptVals i))
    (hacc : acceptB (hornerGatesFrom ptsOf bitOf digOf n nbits acc0 fresh0).1 a = true) :
    PointIsZ a (hornerGatesFrom ptsOf bitOf digOf n nbits acc0 fresh0).2.1.1
      (hornerGatesFrom ptsOf bitOf digOf n nbits acc0 fresh0).2.1.2.1
      (hornerGatesFrom ptsOf bitOf digOf n nbits acc0 fresh0).2.1.2.2
      (hornerRefFrom ptVals (fun pl i => bitAt a (bitOf pl i)) n nbits av0) :=
  foldl_hornerPlaneStep_forces a ptsOf bitOf digOf n ptVals hP
    (List.range nbits) [] acc0 fresh0 av0 hav0 hacc

#assert_axioms hornerAddStep_prefix
#assert_axioms hornerPlaneStep_prefix
#assert_axioms foldl_hornerAddStep_forces
#assert_axioms foldl_hornerPlaneStep_forces
#assert_axioms hornerGates_forces

/-! ## §3 — ⚑ THE SKIP ARGUMENT DOES NOT EXIST, PROVED.

`PastaMsmAir` §6.2 named the obstruction in prose: "a Horner AIR must emit a row for every
(plane, term) pair or prove the skipped ones had a zero bit". Here it is as a theorem.

An emitted constraint list is produced by a `def` whose arguments are COLUMN INDICES and COUNTS.
`Assignment` does not occur in the type of `hornerGatesFrom`. The consequence is
`horner_layout_is_witness_independent`: any two layouts at the same `(n, nbits)` emit the SAME
number of gates. A prover cannot make the trace shorter by having fewer set bits, because the trace
is fixed before any witness exists.

So the `4,161,791` set-bit figure (`PastaIpaFold.hornerAdds 15 255`) is **not the height of any
emitted trace**, and the emitted height is `nbits·(n+1)`. -/

/-- Core gates per conditional-add digit selector. -/
def SEL_GATES : Nat := 4
/-- Caller-supplied columns per conditional-add digit (1 bit + 27 digit limbs). -/
def SEL_COLS : Nat := 28

theorem condPointGates_length (bCol pX pY pZ dX dY dZ : Nat) :
    (condPointGates bCol pX pY pZ dX dY dZ).length = SEL_GATES := rfl

/-- One `(plane, term)` step: the selector plus one RCB add. -/
theorem hornerAddStep_one (ptsOf : Nat → Nat × Nat × Nat) (bitOf : Nat → Nat)
    (digOf : Nat → Nat × Nat × Nat) (st : List VmConstraint2 × (Nat × Nat × Nat) × Nat) (t : Nat) :
    (hornerAddStep ptsOf bitOf digOf st t).1.length = st.1.length + (SEL_GATES + RCB_GATES)
    ∧ (hornerAddStep ptsOf bitOf digOf st t).2.2 = st.2.2 + RCB_COLS := by
  constructor
  · simp only [hornerAddStep, List.length_append, condPointGates_length,
      pallasCompleteAdd_length, SEL_GATES, RCB_GATES]
  · simp only [hornerAddStep, pallasCompleteAdd_fresh, RCB_COLS]

theorem hornerAddStep_counts (ptsOf : Nat → Nat × Nat × Nat) (bitOf : Nat → Nat)
    (digOf : Nat → Nat × Nat × Nat) : ∀ (ts : List Nat)
    (st : List VmConstraint2 × (Nat × Nat × Nat) × Nat),
    (ts.foldl (hornerAddStep ptsOf bitOf digOf) st).1.length
      = st.1.length + (SEL_GATES + RCB_GATES) * ts.length
    ∧ (ts.foldl (hornerAddStep ptsOf bitOf digOf) st).2.2 = st.2.2 + RCB_COLS * ts.length := by
  intro ts
  induction ts with
  | nil => intro st; simp
  | cons t rest ih =>
    intro st
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (hornerAddStep ptsOf bitOf digOf st t)
    obtain ⟨e1, e2⟩ := hornerAddStep_one ptsOf bitOf digOf st t
    rw [h1, h2, e1, e2, List.length_cons]
    exact ⟨by ring, by ring⟩

theorem hornerPlaneStep_one (ptsOf : Nat → Nat × Nat × Nat) (bitOf : Nat → Nat → Nat)
    (digOf : Nat → Nat → Nat × Nat × Nat) (n : Nat)
    (st : List VmConstraint2 × (Nat × Nat × Nat) × Nat) (t : Nat) :
    (hornerPlaneStep ptsOf bitOf digOf n st t).1.length
      = st.1.length + (RCB_GATES + (SEL_GATES + RCB_GATES) * n)
    ∧ (hornerPlaneStep ptsOf bitOf digOf n st t).2.2 = st.2.2 + RCB_COLS * (n + 1) := by
  obtain ⟨h1, h2⟩ := hornerAddStep_counts ptsOf (bitOf t) (digOf t) (List.range n)
    ([], (pallasCompleteAdd st.2.1.1 st.2.1.2.1 st.2.1.2.2
            st.2.1.1 st.2.1.2.1 st.2.1.2.2 st.2.2).2.1,
         (pallasCompleteAdd st.2.1.1 st.2.1.2.1 st.2.1.2.2
            st.2.1.1 st.2.1.2.1 st.2.1.2.2 st.2.2).2.2)
  rw [List.length_range] at h1 h2
  simp only [hornerPlaneStep, List.length_append, List.length_nil, Nat.zero_add,
    pallasCompleteAdd_length, pallasCompleteAdd_fresh, SEL_GATES, RCB_GATES,
    RCB_COLS] at h1 h2 ⊢
  omega

/-- Core gates of the whole emitted bit-plane scan. -/
def hornerGateCount (n nbits : Nat) : Nat := nbits * (RCB_GATES + (SEL_GATES + RCB_GATES) * n)
/-- RCB-intermediate columns of the whole emitted scan. -/
def hornerColCount (n nbits : Nat) : Nat := nbits * (RCB_COLS * (n + 1))
/-- Caller-supplied selector columns of the whole emitted scan. -/
def hornerSelColCount (n nbits : Nat) : Nat := nbits * (SEL_COLS * n)

/-- ⚑ **`hornerGates_counts`** — the closed-form price of the emitted scan, at every `(n, nbits)`
at once. Proved by induction; evaluated at no `n` in particular, which is what makes it an
INSTRUMENT and not a measurement of one instance. -/
theorem hornerGates_counts (ptsOf : Nat → Nat × Nat × Nat) (bitOf : Nat → Nat → Nat)
    (digOf : Nat → Nat → Nat × Nat × Nat) (n nbits : Nat) (acc0 : Nat × Nat × Nat)
    (fresh0 : Nat) :
    (hornerGatesFrom ptsOf bitOf digOf n nbits acc0 fresh0).1.length = hornerGateCount n nbits
    ∧ (hornerGatesFrom ptsOf bitOf digOf n nbits acc0 fresh0).2.2
        = fresh0 + hornerColCount n nbits := by
  have key : ∀ (ts : List Nat) (st : List VmConstraint2 × (Nat × Nat × Nat) × Nat),
      (ts.foldl (hornerPlaneStep ptsOf bitOf digOf n) st).1.length
        = st.1.length + (RCB_GATES + (SEL_GATES + RCB_GATES) * n) * ts.length
      ∧ (ts.foldl (hornerPlaneStep ptsOf bitOf digOf n) st).2.2
        = st.2.2 + (RCB_COLS * (n + 1)) * ts.length := by
    intro ts
    induction ts with
    | nil => intro st; simp
    | cons t rest ih =>
      intro st
      rw [List.foldl_cons]
      obtain ⟨h1, h2⟩ := ih (hornerPlaneStep ptsOf bitOf digOf n st t)
      obtain ⟨e1, e2⟩ := hornerPlaneStep_one ptsOf bitOf digOf n st t
      rw [h1, h2, e1, e2, List.length_cons]
      exact ⟨by ring, by ring⟩
  obtain ⟨h1, h2⟩ := key (List.range nbits) ([], acc0, fresh0)
  rw [List.length_range] at h1 h2
  refine ⟨?_, ?_⟩
  · rw [hornerGatesFrom, h1, hornerGateCount]
    simp only [List.length_nil, Nat.zero_add]
    ring
  · rw [hornerGatesFrom, h2, hornerColCount]; ring

/-- ⚑⚑ **`horner_layout_is_witness_independent`** — **the emitted gate count does not depend on the
layout, and there is no `Assignment` for it to depend on.** This is the skip argument, refuted: a
circuit cannot be shorter because a scalar happened to have fewer set bits, because the constraint
list is fixed before any witness exists. -/
theorem horner_layout_is_witness_independent
    (pts1 pts2 : Nat → Nat × Nat × Nat) (bit1 bit2 : Nat → Nat → Nat)
    (dig1 dig2 : Nat → Nat → Nat × Nat × Nat) (n nbits : Nat)
    (acc1 acc2 : Nat × Nat × Nat) (f1 f2 : Nat) :
    (hornerGatesFrom pts1 bit1 dig1 n nbits acc1 f1).1.length
      = (hornerGatesFrom pts2 bit2 dig2 n nbits acc2 f2).1.length := by
  rw [(hornerGates_counts pts1 bit1 dig1 n nbits acc1 f1).1,
      (hornerGates_counts pts2 bit2 dig2 n nbits acc2 f2).1]

/-- The same statement for the term-by-term MSM of `PastaMsmAir` (which had the property all along;
it was never said). -/
theorem msm_layout_is_witness_independent
    (d1 d2 : Nat → List (Nat × Nat × Nat)) (nDigits : Nat) (z1 z2 : Nat × Nat × Nat)
    (n : Nat) (acc1 acc2 : Nat × Nat × Nat) (f1 f2 : Nat) :
    (Dregg2.Circuit.Emit.PastaMsmAir.msmGatesFrom d1 nDigits z1 n acc1 f1).1.length
      = (Dregg2.Circuit.Emit.PastaMsmAir.msmGatesFrom d2 nDigits z2 n acc2 f2).1.length := by
  obtain ⟨h1, _⟩ := Dregg2.Circuit.Emit.PastaMsmAir.msmGatesFrom_counts d1 nDigits z1
    (List.range n) ([], acc1, f1)
  obtain ⟨h2, _⟩ := Dregg2.Circuit.Emit.PastaMsmAir.msmGatesFrom_counts d2 nDigits z2
    (List.range n) ([], acc2, f2)
  rw [Dregg2.Circuit.Emit.PastaMsmAir.msmGatesFrom,
      Dregg2.Circuit.Emit.PastaMsmAir.msmGatesFrom, h1, h2]

#assert_axioms hornerGates_counts
#assert_axioms horner_layout_is_witness_independent
#assert_axioms msm_layout_is_witness_independent

/-- **RCB complete adds** the emitted scan performs: one doubling per plane, one conditional add
per (plane, term). THE row unit, and it is what `horner_layout_is_witness_independent` pins. -/
def hornerRcbAdds (n nbits : Nat) : Nat := nbits * (n + 1)

/-- `PastaIpaFold.hornerAdds` — the SET-BIT count, at an average Hamming weight of `nbits/2`.
Reproduced here only to be refuted as a layout. -/
def hornerSetBitAdds (k nbits : Nat) : Nat := nbits + 2 ^ k * (nbits / 2)

-- The emitted height is 2.008× the set-bit count, at Mina's wrap SRS shape.
#guard hornerRcbAdds 32768 255 == 8356095
#guard hornerSetBitAdds 15 255 == 4161791
#guard 2 * hornerSetBitAdds 15 255 < hornerRcbAdds 32768 255
#guard hornerRcbAdds 32768 255 < 3 * hornerSetBitAdds 15 255
-- ⚑ And the Horner win over term-by-term is 2×, NOT the 4× a set-bit reading suggests.
#guard openingCheckRcbAdds 32768 255 == 16744449
#guard 2 * hornerRcbAdds 32768 255 < openingCheckRcbAdds 32768 255
#guard openingCheckRcbAdds 32768 255 < 3 * hornerRcbAdds 32768 255
-- Emitted gate/column counts at the same shape.
#guard hornerGateCount 32768 255 == 309174495
#guard hornerRcbAdds 32768 255 * RCB_COLS == 3693393990

/-! The counts theorem checked against a MATERIALISED generator at a small instance, so the closed
form is verified AGAINST the emitted list and not merely asserted about it (`PastaMsmAir` §5's
instrument). A `#guard` at `n = 32768` would ask the kernel to build a 300-million-element list. -/
#guard (hornerGatesFrom (fun i => (100 + i * 27, 109 + i * 27, 118 + i * 27))
          (fun pl i => 900 + pl * 10 + i)
          (fun pl i => (2000 + pl * 100 + i * 27, 2009 + pl * 100 + i * 27,
                        2018 + pl * 100 + i * 27))
          3 2 (0, 9, 18) 5000).1.length == hornerGateCount 3 2
#guard (hornerGatesFrom (fun i => (100 + i * 27, 109 + i * 27, 118 + i * 27))
          (fun pl i => 900 + pl * 10 + i)
          (fun pl i => (2000 + pl * 100 + i * 27, 2009 + pl * 100 + i * 27,
                        2018 + pl * 100 + i * 27))
          3 2 (0, 9, 18) 5000).2.2 == 5000 + hornerColCount 3 2
#guard hornerGateCount 3 2 == 288
-- …and the emitted list is NOT empty, so `hornerGates_forces` is a theorem about real gates.
#guard 0 < hornerGateCount 3 2

/-! ## §4 — ⚑ THE GLV DIGIT SELECTOR, built.

`PastaMsmAir` §6.6: "the digits are represented inputs, not derived … a verifier that must CHECK
the scalar decomposition needs K2's endo recomposition gate. Named, not built." Built here.

The digit is the entry of the 4-element table `{O, P, φP, P+φP}` that two witness bits select.
`φP` is K2's `pallasEndoGadget` (the ζ pin plus ONE `fpMul`, 2 core gates, ζ pinned in-circuit);
`P+φP` is one RCB add. Both are per-TERM precomputes, not per-digit — which is the whole point.

Degree discipline: the four selector coefficients `s₀₀ = 1−b₁−b₂+m`, `s₁₀ = b₁−m`, `s₀₁ = b₂−m`,
`s₁₁ = m` are LINEAR once `m = b₁·b₂` is witnessed (one degree-2 gate), so each coordinate gate is
`linear × value-head` — degree 2, the same degree `fpMulCore` already carries. **6 core gates.** -/

/-- The reference: the table entry the two bits select. -/
def glvRef (c1 c2 : Bool) (P Q R : PtP) : PtP :=
  if c2 then (if c1 then R else Q) else (if c1 then P else (0, 1, 0))

/-- `b₁·b₂ − m` — the one degree-2 gate, witnessing the AND of the two selector bits. -/
def glvProdHead (b1 b2 m : Nat) : Head := ((Head.lin 1 b1).mul (Head.lin 1 b2)).addLin (-1) m

/-- `s₁₀ = b₁ − m`. -/ def s10H (b1 m : Nat) : Head := (Head.lin 1 b1).addLin (-1) m
/-- `s₀₁ = b₂ − m`. -/ def s01H (b2 m : Nat) : Head := (Head.lin 1 b2).addLin (-1) m
/-- `s₁₁ = m`. -/      def s11H (m : Nat) : Head := Head.lin 1 m
/-- `s₀₀ = 1 − b₁ − b₂ + m`. -/
def s00H (b1 b2 m : Nat) : Head := (((Head.c 1).addLin (-1) b1).addLin (-1) b2).addLin 1 m

/-- A coordinate whose `O`-entry is `0` (the `X` and `Z` coordinates). -/
def glvZeroHead (b1 b2 m pC qC rC dC : Nat) : Head :=
  ((((s10H b1 m).mul (fpValue pC)).append ((s01H b2 m).mul (fpValue qC))).append
    ((s11H m).mul (fpValue rC))).append ((fpValue dC).scale (-1))

/-- The `Y` coordinate, whose `O`-entry is `1`. -/
def glvOneHead (b1 b2 m pC qC rC dC : Nat) : Head :=
  (glvZeroHead b1 b2 m pC qC rC dC).append (s00H b1 b2 m)

theorem glvZeroHead_eval (a : Assignment) (b1 b2 m pC qC rC dC : Nat) :
    evalH (glvZeroHead b1 b2 m pC qC rC dC) a
      = (a b1 - a m) * fpVal a pC + (a b2 - a m) * fpVal a qC + a m * fpVal a rC
        - fpVal a dC := by
  simp only [glvZeroHead, s10H, s01H, s11H, evalH_append, evalH_scale, evalH_mul, evalH_addLin,
    evalH_lin, fpVal_eq]
  ring

theorem glvOneHead_eval (a : Assignment) (b1 b2 m pC qC rC dC : Nat) :
    evalH (glvOneHead b1 b2 m pC qC rC dC) a
      = (a b1 - a m) * fpVal a pC + (a b2 - a m) * fpVal a qC + a m * fpVal a rC
        - fpVal a dC + (1 - a b1 - a b2 + a m) := by
  simp only [glvOneHead, s00H, evalH_append, evalH_addLin, evalH_c, glvZeroHead_eval]
  ring

/-- **`glvDigitGates`** — the GLV digit: **6 core gates** (two bit pins, one AND witness, three
coordinate selects). -/
def glvDigitGates (b1 b2 m pX pY pZ qX qY qZ rX rY rZ dX dY dZ : Nat) : List VmConstraint2 :=
  [ binGate b1, binGate b2, cgH (glvProdHead b1 b2 m)
  , cgH (glvZeroHead b1 b2 m pX qX rX dX)
  , cgH (glvOneHead b1 b2 m pY qY rY dY)
  , cgH (glvZeroHead b1 b2 m pZ qZ rZ dZ) ]

/-- ⚑ **`glvDigit_forces`** — the emitted selector FORCES the digit columns to represent exactly
the table entry the assignment's own two bits select. This is `PastaMsmAir` §6.6 closed: the digit
is no longer a represented input a prover may choose freely; it is DERIVED from the bits. -/
theorem glvDigit_forces (a : Assignment) (b1 b2 m pX pY pZ qX qY qZ rX rY rZ dX dY dZ : Nat)
    {P Q R : PtP}
    (hP : PointIsZ a pX pY pZ P) (hQ : PointIsZ a qX qY qZ Q) (hR : PointIsZ a rX rY rZ R)
    (hacc : acceptB (glvDigitGates b1 b2 m pX pY pZ qX qY qZ rX rY rZ dX dY dZ) a = true) :
    PointIsZ a dX dY dZ (glvRef (bitAt a b1) (bitAt a b2) P Q R) := by
  simp only [glvDigitGates, acceptB, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true, gateBodyEvalZero_cgH] at hacc
  obtain ⟨hb1, hb2, hm, gX, gY, gZ⟩ := hacc
  have hmv : a m = a b1 * a b2 := by
    have := of_decide_eq_true hm
    simp only [glvProdHead, evalH_addLin, evalH_mul, evalH_lin] at this
    linarith
  have hX : (a b1 - a m) * fpVal a pX + (a b2 - a m) * fpVal a qX + a m * fpVal a rX
      - fpVal a dX = 0 := by
    have h := of_decide_eq_true gX; rwa [glvZeroHead_eval] at h
  have hY : (a b1 - a m) * fpVal a pY + (a b2 - a m) * fpVal a qY + a m * fpVal a rY
      - fpVal a dY + (1 - a b1 - a b2 + a m) = 0 := by
    have h := of_decide_eq_true gY; rwa [glvOneHead_eval] at h
  have hZ : (a b1 - a m) * fpVal a pZ + (a b2 - a m) * fpVal a qZ + a m * fpVal a rZ
      - fpVal a dZ = 0 := by
    have h := of_decide_eq_true gZ; rwa [glvZeroHead_eval] at h
  obtain ⟨hPx, hPy, hPz⟩ := hP
  obtain ⟨hQx, hQy, hQz⟩ := hQ
  obtain ⟨hRx, hRy, hRz⟩ := hR
  rw [hmv] at hX hY hZ
  rcases binGate_forces a b1 hb1 with e1 | e1 <;> rcases binGate_forces a b2 hb2 with e2 | e2 <;>
    rw [e1, e2] at hX hY hZ
  · -- (0,0) : the point at infinity
    have h1 : bitAt a b1 = false := by simp [bitAt, e1]
    have h2 : bitAt a b2 = false := by simp [bitAt, e2]
    refine ⟨?_, ?_, ?_⟩ <;> simp only [h1, h2, glvRef]
    · rw [show fpVal a dX = 0 by linarith]; simp
    · rw [show fpVal a dY = 1 by linarith]; simp
    · rw [show fpVal a dZ = 0 by linarith]; simp
  · -- (0,1) : φP
    have h1 : bitAt a b1 = false := by simp [bitAt, e1]
    have h2 : bitAt a b2 = true := by simp [bitAt, e2]
    refine ⟨?_, ?_, ?_⟩ <;> simp only [h1, h2, glvRef, if_true]
    · rw [show fpVal a dX = fpVal a qX by linarith]; exact hQx
    · rw [show fpVal a dY = fpVal a qY by linarith]; exact hQy
    · rw [show fpVal a dZ = fpVal a qZ by linarith]; exact hQz
  · -- (1,0) : P
    have h1 : bitAt a b1 = true := by simp [bitAt, e1]
    have h2 : bitAt a b2 = false := by simp [bitAt, e2]
    refine ⟨?_, ?_, ?_⟩ <;> simp only [h1, h2, glvRef, if_true]
    · rw [show fpVal a dX = fpVal a pX by linarith]; exact hPx
    · rw [show fpVal a dY = fpVal a pY by linarith]; exact hPy
    · rw [show fpVal a dZ = fpVal a pZ by linarith]; exact hPz
  · -- (1,1) : P + φP
    have h1 : bitAt a b1 = true := by simp [bitAt, e1]
    have h2 : bitAt a b2 = true := by simp [bitAt, e2]
    refine ⟨?_, ?_, ?_⟩ <;> simp only [h1, h2, glvRef, if_true]
    · rw [show fpVal a dX = fpVal a rX by linarith]; exact hRx
    · rw [show fpVal a dY = fpVal a rY by linarith]; exact hRy
    · rw [show fpVal a dZ = fpVal a rZ by linarith]; exact hRz

#assert_axioms glvZeroHead_eval
#assert_axioms glvOneHead_eval
#assert_axioms glvDigit_forces

/-! ### §4b — the GLV selector BITES at all FOUR selections, and refuses a fifth.

Without the first four `#guard`s, `glvDigit_forces` could be true because its hypothesis is
unsatisfiable — the failure mode `fpIsZeroCore` was built to avoid. The last three are the attacks:
a witnessed AND that is not the AND, and a digit that is not the selected entry. -/

/-- Layout: `b₁, b₂, m` at 0/1/2; `P` at 3/12/21, `Q` at 30/39/48, `R` at 57/66/75; digit at
84/93/102. -/
def glvAsg (c1 c2 : Bool) (px py pz qx qy qz rx ry rz : Nat) : Assignment := fun col =>
  let dx := if c2 then (if c1 then rx else qx) else (if c1 then px else 0)
  let dy := if c2 then (if c1 then ry else qy) else (if c1 then py else 1)
  let dz := if c2 then (if c1 then rz else qz) else (if c1 then pz else 0)
  if col = 0 then (if c1 then 1 else 0)
  else if col = 1 then (if c2 then 1 else 0)
  else if col = 2 then (if c1 && c2 then 1 else 0)
  else if col < 12 then limbOf px (col - 3)
  else if col < 21 then limbOf py (col - 12)
  else if col < 30 then limbOf pz (col - 21)
  else if col < 39 then limbOf qx (col - 30)
  else if col < 48 then limbOf qy (col - 39)
  else if col < 57 then limbOf qz (col - 48)
  else if col < 66 then limbOf rx (col - 57)
  else if col < 75 then limbOf ry (col - 66)
  else if col < 84 then limbOf rz (col - 75)
  else if col < 93 then limbOf dx (col - 84)
  else if col < 102 then limbOf dy (col - 93)
  else if col < 111 then limbOf dz (col - 102)
  else 0

def glvGates : List VmConstraint2 :=
  glvDigitGates 0 1 2 3 12 21 30 39 48 57 66 75 84 93 102

-- SATISFIABLE at every one of the four table entries.
#guard acceptB glvGates (glvAsg false false 7 11 1 13 17 1 19 23 1) == true
#guard acceptB glvGates (glvAsg true false 7 11 1 13 17 1 19 23 1) == true
#guard acceptB glvGates (glvAsg false true 7 11 1 13 17 1 19 23 1) == true
#guard acceptB glvGates (glvAsg true true 7 11 1 13 17 1 19 23 1) == true
-- REFUTABLE: the AND witness is forged (claims `m = 1` while `b₁ = 0`).
#guard acceptB glvGates (bumpAt (glvAsg false true 7 11 1 13 17 1 19 23 1) 2) == false
-- REFUTABLE: the selected digit is bumped.
#guard acceptB glvGates (bumpAt (glvAsg true true 7 11 1 13 17 1 19 23 1) 84) == false
#guard acceptB glvGates (bumpAt (glvAsg false false 7 11 1 13 17 1 19 23 1) 93) == false
-- REFUTABLE: a selector bit that is not a bit.
#guard acceptB glvGates (bumpAt (glvAsg true false 7 11 1 13 17 1 19 23 1) 1) == false

/-! ## §5 — THE GLV LADDER + THE SCALAR BINDING.

The ladder is `PastaScalarMul`'s, with the digit DERIVED instead of supplied: per step, one selector
(6 gates) and two RCB adds (66). `nDigits` steps. -/

/-- One GLV ladder step: select the digit, double the accumulator, add the digit. -/
def glvStep (bitsOf digOf : Nat → Nat × Nat × Nat) (tP tQ tR : Nat × Nat × Nat) :
    List VmConstraint2 × (Nat × Nat × Nat) × Nat → Nat →
    List VmConstraint2 × (Nat × Nat × Nat) × Nat :=
  fun st t =>
    let sel := glvDigitGates (bitsOf t).1 (bitsOf t).2.1 (bitsOf t).2.2
                 tP.1 tP.2.1 tP.2.2 tQ.1 tQ.2.1 tQ.2.2 tR.1 tR.2.1 tR.2.2
                 (digOf t).1 (digOf t).2.1 (digOf t).2.2
    let dbl := pallasCompleteAdd st.2.1.1 st.2.1.2.1 st.2.1.2.2
                 st.2.1.1 st.2.1.2.1 st.2.1.2.2 st.2.2
    let add := pallasCompleteAdd dbl.2.1.1 dbl.2.1.2.1 dbl.2.1.2.2
                 (digOf t).1 (digOf t).2.1 (digOf t).2.2 dbl.2.2
    (st.1 ++ (sel ++ (dbl.1 ++ add.1)), add.2.1, add.2.2)

/-- The whole GLV ladder over `nDigits` steps. -/
def glvLadderFrom (bitsOf digOf : Nat → Nat × Nat × Nat) (tP tQ tR : Nat × Nat × Nat)
    (nDigits : Nat) (acc0 : Nat × Nat × Nat) (fresh0 : Nat) :
    List VmConstraint2 × (Nat × Nat × Nat) × Nat :=
  (List.range nDigits).foldl (glvStep bitsOf digOf tP tQ tR) ([], acc0, fresh0)

/-- The reference double-and-add fold over the selected table entries. -/
def glvLadderRef (bits : Nat → Bool × Bool) (P Q R : PtP) (nDigits : Nat) (acc0 : PtP) : PtP :=
  (List.range nDigits).foldl
    (fun acc t => rcbAddZmod (rcbAddZmod acc acc) (glvRef (bits t).1 (bits t).2 P Q R)) acc0

theorem glvStep_prefix (bitsOf digOf : Nat → Nat × Nat × Nat) (tP tQ tR : Nat × Nat × Nat) :
    ∀ (ts : List Nat) (Xs : List VmConstraint2) (acc : Nat × Nat × Nat) (fr : Nat),
    ∃ Ys, (ts.foldl (glvStep bitsOf digOf tP tQ tR) (Xs, acc, fr)).1 = Xs ++ Ys := by
  intro ts
  induction ts with
  | nil => intro Xs acc fr; exact ⟨[], by simp⟩
  | cons t rest ih =>
    intro Xs acc fr
    rw [List.foldl_cons]
    obtain ⟨Ys, hY⟩ := ih (glvStep bitsOf digOf tP tQ tR (Xs, acc, fr) t).1
      (glvStep bitsOf digOf tP tQ tR (Xs, acc, fr) t).2.1
      (glvStep bitsOf digOf tP tQ tR (Xs, acc, fr) t).2.2
    refine ⟨(glvDigitGates (bitsOf t).1 (bitsOf t).2.1 (bitsOf t).2.2
              tP.1 tP.2.1 tP.2.2 tQ.1 tQ.2.1 tQ.2.2 tR.1 tR.2.1 tR.2.2
              (digOf t).1 (digOf t).2.1 (digOf t).2.2
             ++ ((pallasCompleteAdd acc.1 acc.2.1 acc.2.2 acc.1 acc.2.1 acc.2.2 fr).1
                 ++ (pallasCompleteAdd
                      (pallasCompleteAdd acc.1 acc.2.1 acc.2.2 acc.1 acc.2.1 acc.2.2 fr).2.1.1
                      (pallasCompleteAdd acc.1 acc.2.1 acc.2.2 acc.1 acc.2.1 acc.2.2 fr).2.1.2.1
                      (pallasCompleteAdd acc.1 acc.2.1 acc.2.2 acc.1 acc.2.1 acc.2.2 fr).2.1.2.2
                      (digOf t).1 (digOf t).2.1 (digOf t).2.2
                      (pallasCompleteAdd acc.1 acc.2.1 acc.2.2 acc.1 acc.2.1 acc.2.2 fr).2.2).1))
            ++ Ys, ?_⟩
    rw [show (glvStep bitsOf digOf tP tQ tR (Xs, acc, fr) t)
        = ((glvStep bitsOf digOf tP tQ tR (Xs, acc, fr) t).1,
           (glvStep bitsOf digOf tP tQ tR (Xs, acc, fr) t).2.1,
           (glvStep bitsOf digOf tP tQ tR (Xs, acc, fr) t).2.2) from rfl] at hY
    rw [hY]; dsimp only [glvStep]; rw [List.append_assoc]

/-- ⚑⚑ **`glvLadder_forces`** — the emitted GLV ladder FORCES the double-and-add fold of the table
entries its own selector bits pick. Digit-count-independent: `nDigits` appears only as a fold
bound, so the statement at `128` is the statement at `1`. -/
theorem glvLadder_forces (a : Assignment) (bitsOf digOf : Nat → Nat × Nat × Nat)
    (tP tQ tR : Nat × Nat × Nat) {P Q R : PtP}
    (hP : PointIsZ a tP.1 tP.2.1 tP.2.2 P) (hQ : PointIsZ a tQ.1 tQ.2.1 tQ.2.2 Q)
    (hR : PointIsZ a tR.1 tR.2.1 tR.2.2 R) :
    ∀ (ts : List Nat) (cs0 : List VmConstraint2) (acc0 : Nat × Nat × Nat) (fr0 : Nat) (av0 : PtP),
      PointIsZ a acc0.1 acc0.2.1 acc0.2.2 av0 →
      acceptB ((ts.foldl (glvStep bitsOf digOf tP tQ tR) (cs0, acc0, fr0)).1) a = true →
      PointIsZ a (ts.foldl (glvStep bitsOf digOf tP tQ tR) (cs0, acc0, fr0)).2.1.1
        (ts.foldl (glvStep bitsOf digOf tP tQ tR) (cs0, acc0, fr0)).2.1.2.1
        (ts.foldl (glvStep bitsOf digOf tP tQ tR) (cs0, acc0, fr0)).2.1.2.2
        (ts.foldl (fun acc t => rcbAddZmod (rcbAddZmod acc acc)
          (glvRef (bitAt a (bitsOf t).1) (bitAt a (bitsOf t).2.1) P Q R)) av0) := by
  intro ts
  induction ts with
  | nil => intro cs0 acc0 fr0 av0 hav0 _; exact hav0
  | cons t rest ih =>
    intro cs0 acc0 fr0 av0 hav0 hacc
    rw [List.foldl_cons] at hacc ⊢
    rw [List.foldl_cons]
    set sel := glvDigitGates (bitsOf t).1 (bitsOf t).2.1 (bitsOf t).2.2
                 tP.1 tP.2.1 tP.2.2 tQ.1 tQ.2.1 tQ.2.2 tR.1 tR.2.1 tR.2.2
                 (digOf t).1 (digOf t).2.1 (digOf t).2.2 with hsel
    set dbl := pallasCompleteAdd acc0.1 acc0.2.1 acc0.2.2 acc0.1 acc0.2.1 acc0.2.2 fr0 with hdbl
    set add := pallasCompleteAdd dbl.2.1.1 dbl.2.1.2.1 dbl.2.1.2.2
                 (digOf t).1 (digOf t).2.1 (digOf t).2.2 dbl.2.2 with hadd
    have hstep : glvStep bitsOf digOf tP tQ tR (cs0, acc0, fr0) t
        = (cs0 ++ (sel ++ (dbl.1 ++ add.1)), add.2.1, add.2.2) := rfl
    rw [hstep] at hacc ⊢
    obtain ⟨Ys, hY⟩ := glvStep_prefix bitsOf digOf tP tQ tR rest
      (cs0 ++ (sel ++ (dbl.1 ++ add.1))) _ _
    have haccStep : acceptB (sel ++ (dbl.1 ++ add.1)) a = true := by
      have h1 : acceptB (cs0 ++ (sel ++ (dbl.1 ++ add.1))) a = true :=
        acceptB_prefix (cs0 ++ (sel ++ (dbl.1 ++ add.1))) Ys a (by rw [hY] at hacc; exact hacc)
      exact acceptB_suffix cs0 (sel ++ (dbl.1 ++ add.1)) a h1
    have haccSel : acceptB sel a = true := acceptB_prefix _ _ a haccStep
    have haccRest : acceptB (dbl.1 ++ add.1) a = true := acceptB_suffix _ _ a haccStep
    have haccDbl : acceptB dbl.1 a = true := acceptB_prefix _ _ a haccRest
    have haccAdd : acceptB add.1 a = true := acceptB_suffix _ _ a haccRest
    have hdig : PointIsZ a (digOf t).1 (digOf t).2.1 (digOf t).2.2
        (glvRef (bitAt a (bitsOf t).1) (bitAt a (bitsOf t).2.1) P Q R) :=
      glvDigit_forces a (bitsOf t).1 (bitsOf t).2.1 (bitsOf t).2.2
        tP.1 tP.2.1 tP.2.2 tQ.1 tQ.2.1 tQ.2.2 tR.1 tR.2.1 tR.2.2
        (digOf t).1 (digOf t).2.1 (digOf t).2.2 hP hQ hR haccSel
    have hd : PointIsZ a dbl.2.1.1 dbl.2.1.2.1 dbl.2.1.2.2 (rcbAddZmod av0 av0) :=
      pallasRcbStep_forces a acc0.1 acc0.2.1 acc0.2.2 acc0.1 acc0.2.1 acc0.2.2 fr0
        hav0 hav0 haccDbl
    have hnext : PointIsZ a add.2.1.1 add.2.1.2.1 add.2.1.2.2
        (rcbAddZmod (rcbAddZmod av0 av0)
          (glvRef (bitAt a (bitsOf t).1) (bitAt a (bitsOf t).2.1) P Q R)) :=
      pallasRcbStep_forces a dbl.2.1.1 dbl.2.1.2.1 dbl.2.1.2.2
        (digOf t).1 (digOf t).2.1 (digOf t).2.2 dbl.2.2 hd hdig haccAdd
    exact ih (cs0 ++ (sel ++ (dbl.1 ++ add.1))) _ _ _ hnext hacc

/-- The `List.range` packaging. -/
theorem glvLadderFrom_forces (a : Assignment) (bitsOf digOf : Nat → Nat × Nat × Nat)
    (tP tQ tR : Nat × Nat × Nat) {P Q R : PtP} (nDigits : Nat) (acc0 : Nat × Nat × Nat)
    (fresh0 : Nat) (av0 : PtP)
    (hP : PointIsZ a tP.1 tP.2.1 tP.2.2 P) (hQ : PointIsZ a tQ.1 tQ.2.1 tQ.2.2 Q)
    (hR : PointIsZ a tR.1 tR.2.1 tR.2.2 R)
    (hav0 : PointIsZ a acc0.1 acc0.2.1 acc0.2.2 av0)
    (hacc : acceptB (glvLadderFrom bitsOf digOf tP tQ tR nDigits acc0 fresh0).1 a = true) :
    PointIsZ a (glvLadderFrom bitsOf digOf tP tQ tR nDigits acc0 fresh0).2.1.1
      (glvLadderFrom bitsOf digOf tP tQ tR nDigits acc0 fresh0).2.1.2.1
      (glvLadderFrom bitsOf digOf tP tQ tR nDigits acc0 fresh0).2.1.2.2
      (glvLadderRef (fun t => (bitAt a (bitsOf t).1, bitAt a (bitsOf t).2.1)) P Q R nDigits av0) :=
  glvLadder_forces a bitsOf digOf tP tQ tR hP hQ hR (List.range nDigits) [] acc0 fresh0 av0
    hav0 hacc

#assert_axioms glvStep_prefix
#assert_axioms glvLadder_forces
#assert_axioms glvLadderFrom_forces

/-! ### §5a — THE SCALAR BINDING: what makes the halves halves.

Two gate families, both degree 1 in the reconstructed values because `λ` is a CONSTANT:

  * `glvBindHead` — ONE gate forcing `k₁ + λ·k₂ ≡ k (mod q)` with a witnessed quotient. `q = qN` is
    the PALLAS SCALAR field (`= ` the Vesta base field): the group here is Pallas, so its scalars
    live mod `qN` and its lambda is `lambdaPallas`. Getting that backwards is the easy mistake and
    §5b says why.
  * `bitsBindHead` — ONE gate per half forcing the MSB-first recomposition
    `Σ_t 2^(nDigits−1−t)·b_t = k_j` over ℤ. Because it is an ℤ identity (not a congruence), it also
    forces `0 ≤ k_j < 2^nDigits` whenever the bits are pinned — which is what makes `nDigits = 128`
    a REFUSAL and not a hope. -/

/-- `k₁ + λ·k₂ − k − q·quot`. -/
def glvBindHead (k1B k2B kB quotB : Nat) : Head :=
  (((fpValue k1B).append ((fpValue k2B).scale (lambdaPallas : ℤ))).append
    ((fpValue kB).scale (-1))).append ((fpValue quotB).scale (-(qN : ℤ)))

/-- ⚑ **`glvBind_forces`** — a satisfied instance pins `k₁ + λ·k₂ ≡ k` in the Pallas SCALAR field.
With `PastaCurve.pallasEndo_forces` (`φ(P) = ζ·P`) and `lambdaPallas_eq_zetaQ_sq` (the `ipa.rs`
`endos()` recipe — the SQUARE, the subtlety K2 already handled), this is exactly what makes
`[k₁]P + [k₂]φP = [k]P`. -/
theorem glvBind_forces (a : Assignment) (k1B k2B kB quotB : Nat)
    (hg : evalH (glvBindHead k1B k2B kB quotB) a = 0) :
    ((qN : ℤ)) ∣ (fpVal a k1B + (lambdaPallas : ℤ) * fpVal a k2B - fpVal a kB) := by
  simp only [glvBindHead, evalH_append, evalH_scale, fpVal_eq] at hg
  exact ⟨fpVal a quotB, by linarith⟩

/-- `Σ_t 2^(nDigits−1−t)·b_t` — the MSB-first recomposition head (`PastaScalarMul.kDigits`'s
order). -/
def bitsValueHead (bitOf : Nat → Nat) (nDigits : Nat) : Head :=
  (List.range nDigits).foldl (fun h t => h.addLin ((2 : ℤ) ^ (nDigits - 1 - t)) (bitOf t))
    Head.zero

/-- `Σ_t 2^(nDigits−1−t)·b_t − k`. -/
def bitsBindHead (bitOf : Nat → Nat) (nDigits kB : Nat) : Head :=
  (bitsValueHead bitOf nDigits).append ((fpValue kB).scale (-1))

/-- ⚑ **`bitsBind_forces`** — the emitted recomposition gate pins the half to its own bits, over ℤ.
Not a congruence: an ℤ identity, so together with the `binGate`s of §4 it also pins
`0 ≤ k < 2^nDigits`. That is the refusal that makes a 128-digit ladder SOUND for a 255-bit scalar
and not merely shorter. -/
theorem bitsBind_forces (a : Assignment) (bitOf : Nat → Nat) (nDigits kB : Nat)
    (hg : evalH (bitsBindHead bitOf nDigits kB) a = 0) :
    ((List.range nDigits).map (fun t => (2 : ℤ) ^ (nDigits - 1 - t) * a (bitOf t))).sum
      = fpVal a kB := by
  simp only [bitsBindHead, bitsValueHead, evalH_append, evalH_scale, fpVal_eq,
    evalH_foldl_addLinG, evalH_zero, zero_add] at hg
  linarith

#assert_axioms glvBind_forces
#assert_axioms bitsBind_forces

/-! ### §5b — ⚑ THE PALLAS GLV LATTICE, and why the Vesta one does not transfer.

`PicklesTranscriptBinding.glvA/glvB` (Fable's P4) is the Gauss/Lagrange-reduced basis of
`{(x,y) : x ≡ y·lambdaVesta (mod pN)}`. That is **Vesta's** lattice, and it settled `endoMap`
injectivity on 128-bit prechallenges — a real result, reused here in METHOD, not restated.

This AIR is **Pallas** (`pallasCompleteAdd`, base field `pN`, so scalar field `qN`,
`λ = lambdaPallas`). Its lattice is a DIFFERENT one and is reduced here, with the same three
certificates checked in-kernel: the vector lies in the lattice, its Eisenstein norm is `qN` EXACTLY
(the classical confirmation that `qN` splits as `a²+ab+b²` in `ℤ[ω]`, which is precisely the CM
condition `lambdaPallas` being a primitive cube root of unity mod `qN` supplies), and `gcd = 1`.

⚑ **What does NOT transfer, said out loud: the `2^70` minimality bound, and it is not wanted.** At
128-bit halves there are about `2^256/qN ≈ 2^1.5` representations of each scalar, so the
decomposition is NOT unique and no small-relation argument applies. Soundness never needed
uniqueness — `glvBind_forces` accepts ANY representation and every one of them multiplies to the
same point. The lattice is a **completeness** certificate here: it is what says a 128-bit
decomposition EXISTS for the prover to find. -/

/-- The Gauss-reduced shortest-vector coordinate `a` of the PALLAS GLV lattice
`{(x,y) : x ≡ y·lambdaPallas (mod qN)}`. ≈`2^127`. -/
def glvPallasA : ℤ := 98231058071100081932162823354453065728
/-- The `y`-side coordinate. -/
def glvPallasB : ℤ := 98231058071186745657228807397848383489

theorem glvPallas_dvd : (qN : ℤ) ∣ (glvPallasA - glvPallasB * (lambdaPallas : ℤ)) := by decide

theorem glvPallas_eisenstein :
    glvPallasA ^ 2 + glvPallasA * glvPallasB + glvPallasB ^ 2 = (qN : ℤ) := by decide

theorem glvPallas_coprime : Int.gcd glvPallasA glvPallasB = 1 := by decide

theorem glvPallasA_pos : (0 : ℤ) < glvPallasA := by decide
theorem glvPallasB_pos : (0 : ℤ) < glvPallasB := by decide

/-- ⚑ **The basis is SHORT: both coordinates fit in 128 bits.** This is the halving, certified:
a 255-bit Pallas scalar decomposes against a basis whose entries are `< 2^128`, so the ladder needs
`128` steps, not `255`. -/
theorem glvPallas_short : glvPallasA < 2 ^ 128 ∧ glvPallasB < 2 ^ 128 := by decide

/-- …and the basis is genuinely the SHORT one, not a lucky small pair: both coordinates exceed
`2^126`, so it sits within a factor of 4 of `√qN` — no shorter lattice vector hides below it. -/
theorem glvPallas_not_shorter : (2 : ℤ) ^ 126 < glvPallasA ∧ (2 : ℤ) ^ 126 < glvPallasB := by
  decide

/-- `PicklesTranscriptBinding.glvA` — QUOTED, not imported (that file pulls `Mathlib.Tactic` and
the ROM floor; this one stays at the AIR layer). -/
def vestaBasisA : Nat := 98231058071186745657228807397848383488
/-- `PicklesTranscriptBinding.glvB`, quoted. -/
def vestaBasisB : Nat := 98231058071100081932162823354453065729

-- ⚑ The Vesta basis is VESTA's — its Eisenstein norm is `pN` …
#guard vestaBasisA ^ 2 + vestaBasisA * vestaBasisB + vestaBasisB ^ 2 == pN
-- … and NOT `qN`, so nobody can read Fable's numbers as covering this file's curve.
#guard (vestaBasisA ^ 2 + vestaBasisA * vestaBasisB + vestaBasisB ^ 2 == qN) == false
-- And §5b's basis is the mirror image: the Pallas one, off the Vesta pair by ±1 in each coordinate.
#guard (glvPallasA + 1 : ℤ) == (vestaBasisB : ℤ)
#guard (glvPallasB - 1 : ℤ) == (vestaBasisA : ℤ)

#assert_axioms glvPallas_dvd
#assert_axioms glvPallas_eisenstein
#assert_axioms glvPallas_coprime
#assert_axioms glvPallas_short
#assert_axioms glvPallas_not_shorter

/-! ## §6 — ⚑ THE RE-PRICING, as theorems.

Row unit: one RCB complete add. Widths are stated but the row is what FRI charges
(`F ≈ 0.094 ms` per trace row for the fold; the width term `c·k·n` is separate and NOT folded in
below — see §7.4). -/

/-- Core gates per GLV digit selector. -/
def GLV_SEL_GATES : Nat := 6
/-- Caller-supplied columns per GLV digit (3 selector columns + 27 digit limbs). -/
def GLV_SEL_COLS : Nat := 30

theorem glvDigitGates_length (b1 b2 m pX pY pZ qX qY qZ rX rY rZ dX dY dZ : Nat) :
    (glvDigitGates b1 b2 m pX pY pZ qX qY qZ rX rY rZ dX dY dZ).length = GLV_SEL_GATES := rfl

theorem glvStep_one (bitsOf digOf : Nat → Nat × Nat × Nat) (tP tQ tR : Nat × Nat × Nat)
    (st : List VmConstraint2 × (Nat × Nat × Nat) × Nat) (t : Nat) :
    (glvStep bitsOf digOf tP tQ tR st t).1.length
      = st.1.length + (GLV_SEL_GATES + 2 * RCB_GATES)
    ∧ (glvStep bitsOf digOf tP tQ tR st t).2.2 = st.2.2 + 2 * RCB_COLS := by
  constructor
  · simp only [glvStep, List.length_append, glvDigitGates_length, pallasCompleteAdd_length,
      GLV_SEL_GATES, RCB_GATES]
  · simp only [glvStep, pallasCompleteAdd_fresh, RCB_COLS]

/-- **`glvLadderFrom_counts`** — the closed-form price of the GLV ladder, at every digit count. -/
theorem glvLadderFrom_counts (bitsOf digOf : Nat → Nat × Nat × Nat)
    (tP tQ tR : Nat × Nat × Nat) (nDigits : Nat) (acc0 : Nat × Nat × Nat) (fresh0 : Nat) :
    (glvLadderFrom bitsOf digOf tP tQ tR nDigits acc0 fresh0).1.length
      = (GLV_SEL_GATES + 2 * RCB_GATES) * nDigits
    ∧ (glvLadderFrom bitsOf digOf tP tQ tR nDigits acc0 fresh0).2.2
      = fresh0 + 2 * RCB_COLS * nDigits := by
  have key : ∀ (ts : List Nat) (st : List VmConstraint2 × (Nat × Nat × Nat) × Nat),
      (ts.foldl (glvStep bitsOf digOf tP tQ tR) st).1.length
        = st.1.length + (GLV_SEL_GATES + 2 * RCB_GATES) * ts.length
      ∧ (ts.foldl (glvStep bitsOf digOf tP tQ tR) st).2.2
        = st.2.2 + (2 * RCB_COLS) * ts.length := by
    intro ts
    induction ts with
    | nil => intro st; simp
    | cons t rest ih =>
      intro st
      rw [List.foldl_cons]
      obtain ⟨h1, h2⟩ := ih (glvStep bitsOf digOf tP tQ tR st t)
      obtain ⟨e1, e2⟩ := glvStep_one bitsOf digOf tP tQ tR st t
      rw [h1, h2, e1, e2, List.length_cons]
      exact ⟨by ring, by ring⟩
  obtain ⟨h1, h2⟩ := key (List.range nDigits) ([], acc0, fresh0)
  rw [List.length_range] at h1 h2
  refine ⟨?_, ?_⟩
  · rw [glvLadderFrom, h1]; simp
  · rw [glvLadderFrom, h2]

#assert_axioms glvLadderFrom_counts

/-! And the GLV ladder's closed form, checked against its own materialised generator. -/
#guard (glvLadderFrom (fun t => (900 + 3 * t, 901 + 3 * t, 902 + 3 * t))
          (fun t => (2000 + t * 27, 2009 + t * 27, 2018 + t * 27))
          (0, 9, 18) (27, 36, 45) (54, 63, 72) 4 (81, 90, 99) 5000).1.length
        == (GLV_SEL_GATES + 2 * RCB_GATES) * 4
#guard (glvLadderFrom (fun t => (900 + 3 * t, 901 + 3 * t, 902 + 3 * t))
          (fun t => (2000 + t * 27, 2009 + t * 27, 2018 + t * 27))
          (0, 9, 18) (27, 36, 45) (54, 63, 72) 4 (81, 90, 99) 5000).2.2
        == 5000 + 2 * RCB_COLS * 4
#guard (GLV_SEL_GATES + 2 * RCB_GATES) * 4 == 288
-- One GLV step costs 72 core gates against the ladder's 66: the selector is 9% of the step, and
-- it buys HALF the steps. That trade is the whole of §6a.
#guard GLV_SEL_GATES + 2 * RCB_GATES == 72
#guard 2 * RCB_GATES == 66

/-! ### §6a — statement (B): the opening relation, 34 terms.

Per term the GLV route pays `nDigits` ladder steps (2 RCB adds each), ONE RCB add to build the
table entry `P + φP`, and ONE to accumulate into the running total. `φP` is 2 core gates and no
RCB add (K2's `pallasEndoGadget`). `delta` enters at coefficient 1: one final add. -/

/-- RCB complete adds of the GLV-route opening check. -/
def glvOpeningRcbAdds (n nDigits : Nat) : Nat := n * (2 * nDigits + 2) + 1
/-- Core gates of the GLV-route opening check (the 2 endo gates per term included). -/
def glvOpeningGateCount (n nDigits : Nat) : Nat :=
  n * ((GLV_SEL_GATES + 2 * RCB_GATES) * nDigits + 2 * RCB_GATES + 2) + RCB_GATES + 2

-- ⚑ STATEMENT (B), 34 terms. `255 → 128` digits.
#guard openingCheckRcbAdds 34 255 == 17375
#guard glvOpeningRcbAdds 34 128 == 8773
#guard openingCheckGateCount 34 255 == 573377
#guard glvOpeningGateCount 34 128 == 315691
-- The halving, as an inequality rather than a slogan: strictly under 51%, and above 50%.
#guard 2 * glvOpeningRcbAdds 34 128 > openingCheckRcbAdds 34 255
#guard 100 * glvOpeningRcbAdds 34 128 < 51 * openingCheckRcbAdds 34 255
-- Both fit ONE deployed root segment; GLV at 13.4% of its height instead of 26.5%.
#guard glvOpeningRcbAdds 34 128 < DREGG_ROOT_ROWS
#guard 7 * glvOpeningRcbAdds 34 128 < DREGG_ROOT_ROWS
#guard 4 * openingCheckRcbAdds 34 255 > DREGG_ROOT_ROWS
-- Per-row width: the RCB add plus the GLV selector, still well inside `MAX_TRACE_WIDTH`.
#guard RCB_COLS + GLV_SEL_COLS == 472
#guard RCB_COLS + GLV_SEL_COLS < DREGG_MAX_WIDTH

/-! ### §6b — ⚑ statement (A): the `⟨s, srs.g⟩` leg, 32,768 terms — every emitted layout.

The non-obvious one. **GLV halves the SERIAL doubling depth; the bit-plane scan has already
amortised that depth to nothing.** Treating `φPᵢ` as a separate term would double `n` to halve
`nbits` — a wash, and by `hornerRcbAdds`'s `+1` per plane a slight LOSS. The 4-entry table of §4
recovers the win, because it halves `nbits` while leaving `n` alone. -/

/-- Bit-plane scan with the GLV 4-entry table: `nbits` planes, `n+1` adds each, plus ONE RCB add
per term to build `Pᵢ + φPᵢ`. -/
def glvHornerRcbAdds (n nbits : Nat) : Nat := nbits * (n + 1) + n
/-- …and with the table entries supplied as PUBLIC constants — legitimate for statement (A),
because `srs.g` is public and so are `φ(srs.gᵢ)` and `srs.gᵢ + φ(srs.gᵢ)`. -/
def glvHornerRcbAddsPublic (n nbits : Nat) : Nat := nbits * (n + 1)

-- ⚑ GLV as a SEPARATE TERM is a wash — strictly worse than plain Horner. Measured, not asserted.
#guard hornerRcbAdds 65536 128 == 8388736
#guard hornerRcbAdds 32768 255 == 8356095
#guard hornerRcbAdds 65536 128 > hornerRcbAdds 32768 255
-- ⚑ GLV as a 4-ENTRY TABLE is the 2× — and it is the best this vocabulary emits.
#guard glvHornerRcbAdds 32768 128 == 4227200
#guard glvHornerRcbAddsPublic 32768 128 == 4194432
#guard 2 * glvHornerRcbAdds 32768 128 > hornerRcbAdds 32768 255
-- ⚑⚑ AND EVERY ONE OF THEM IS PAST THE HARD CEILING. `2^21` is BabyBear's two-adicity at
-- `log_blowup = 6`, a p3 panic — not a prover knob and not a repo check.
#guard DREGG_MAX_ROWS == 2097152
#guard openingCheckRcbAdds 32768 255 > 7 * DREGG_MAX_ROWS
#guard hornerRcbAdds 32768 255 > 3 * DREGG_MAX_ROWS
#guard glvHornerRcbAdds 32768 128 > 2 * DREGG_MAX_ROWS
#guard glvHornerRcbAddsPublic 32768 128 > 2 * DREGG_MAX_ROWS
-- ⚑ The best layout misses `2^22` — the ceiling ONE BLOWUP STEP DOWN — by exactly the 128
-- doublings. `4194432 − 4194304 = 128`. That is how close, and it is still a rate change.
#guard glvHornerRcbAddsPublic 32768 128 - 4194304 == 128
-- Root segments, at `WRAP_LOG_CEIL = 16`.
#guard (openingCheckRcbAdds 32768 255 + DREGG_ROOT_ROWS - 1) / DREGG_ROOT_ROWS == 256
#guard (hornerRcbAdds 32768 255 + DREGG_ROOT_ROWS - 1) / DREGG_ROOT_ROWS == 128
#guard (glvHornerRcbAdds 32768 128 + DREGG_ROOT_ROWS - 1) / DREGG_ROOT_ROWS == 65

/-! ## §7 — ⚑ THE RECOMMENDATION, and the residuals, at CURRENT resolution.

**1. Statement (B): build GLV. It is built.** `17,375 → 8,773` rows, `573,377 → 315,691` gates,
one root segment at 13.4% instead of 26.5%. And the larger half of the win is not the speed: §4 and
§5a close `PastaMsmAir` §6.6, so the ladder's digits are DERIVED from bits the AIR pins rather than
supplied by the prover. The old shape forced a fold of whatever points a prover handed it.

**2. Statement (A): DO NOT OPTIMISE IT. DEFER IT, exactly as Pickles does.** Every emitted layout
is past the two-adicity ceiling (§6b): `7.98×`, `3.98×`, `2.016×`. The last is the floor of this
vocabulary, and `2^21` is a property of BabyBear, not of dregg — you cannot buy past it with an
algorithm. Meanwhile `PastaIPA.sVec_eq_bPoly` already proves the thing deferral needs: `k = 15`
challenges determine all `2^15` scalars, so the accumulator carries 15 field elements instead of
32,768 group elements. Pickles defers this leg for the identical reason, and dregg's own
`Accumulator::accumulate` is the same shape. **Deferral is not skipping the check; it is batching
it** — `N` deferred claims fold into one, and the amortised cost of the final MSM goes to zero in
`N`, which no amount of layout work can match.

The measurement that decides it: `2.016 ×  2^21` versus `O(1)` per block. Optimising further buys
a constant factor on an object that batching removes entirely.

**3. What a bucket/Pippenger layout would need, since it is the one algorithm that WOULD fit.**
`O(n·b/c + 2^c·b/c)` lands near `10^6` rows at `c = 13` — under `2^21`. It does not fit here, and
the reason is precise rather than vague: bucket accumulation is data-dependent ROUTING, and the
descriptor IR reaches no general lookup. `VmConstraint2` has no permutation/sort constraint kind,
and `TableSem` offers only `Range{bits}` and `ExactPublicRows` — verifier-known constants. The
deployed LogUp machinery is real but hardwired into Rust `Ir2Air` arms. The one door is `MemOp`,
whose address is a general witness-dependent expression under a Blum multiset check; a bucket sort
IS expressible through it, at 2 permutation-bus legs per op, with every address forced into a
declared strictly-increasing boundary table below `2^30`. That is a new prover arm plus a new
emitter, for a constant factor on an object we are recommending be deferred. **It does not fit
in-circuit today, and this is why.**

**4. What §6's row model still assumes, and it is not small.**
  * ⚑ **The `Head`/`cgH` vocabulary is STRAIGHT-LINE.** Every generator in this family and in
    `PastaMsmAir` emits one flat single-row constraint list; "one complete add per row of
    `RCB_COLS` columns" is a RE-LAYOUT nothing emits. `DescriptorIR2.WindowExpr` (`loc`/`nxt`) is
    exactly the two-row primitive a periodic AIR needs and `VmConstraint2` carries a window gate —
    so the IR supports it and this emitter family does not. **Named, not built**, and every row
    figure above is conditional on it.
  * ⚑ **`PastaMsmAir.minaOpeningCheckDesc` would be REFUSED by the deployed prover as written**
    (`traceWidth := 442` while its constraints address columns near `10^7`;
    `descriptor_ir2.rs` rejects `column ≥ trace_width`). It is a shape, not a deployable
    descriptor. No descriptor is added here for the same reason.
  * `MAX_TRACE_WIDTH = 1024` is **advisory** on the deployed IR-v2 path — enforced only on the
    legacy v1 DSL. The real per-row budget is `MAX_CONSTRAINT_DEGREE = 8`, which both selectors
    respect at degree 2.
  * `F ≈ 0.094 ms/row` is the **FRI-fold term only**; the width term `c·k·n` is separate and is
    not priced here at 442–472 columns.
  * `RCB_COLS = 442` is one fresh column per constraint intermediate — an EMITTER choice. The
    deployed prover evaluates constraint bodies symbolically and charges degree, not columns, so
    the stride is conservative.

**5. GLV completeness is MEASURED, not proved.** `glvBind_forces` + `bitsBind_forces` are sound at
every `nDigits`: a prover who cannot exhibit `0 ≤ k₁,k₂ < 2^nDigits` with `k₁ + λk₂ ≡ k` is
REFUSED. That such a decomposition always EXISTS at `nDigits = 128` is prover-side completeness and
is **not** discharged here: it was measured over 5,000 random Pallas scalars (found for all, by
Babai rounding against §5b's basis plus a small translate search) and 20,000 more never needed a
129th bit. A covering-radius argument proves it at `129`; the provable-at-`128` route is the
three-digit `{1, λ, λ²}` variant (`1 + λ + λ² ≡ 0`, so a signed pair shifts to a nonneg triple),
which costs an 8-entry table and one more `fpMul`. Named at the right resolution: soundness proved,
completeness sampled.

**6. Unchanged from `PastaMsmAir` §6.** P10 (passing ≠ knowing) is untouched, and a dregg STARK of
any of these AIRs inherits it plus the FRI floor. `srs.g` remains the largest piece of trusted data.
RCB completeness is inherited (RCB'15 Thm 1) — §4's selector forces coordinates, not group elements.
Canonicity is still ungated. The reality gate and its ten tamper poles are untouched, as they must
be: they are what says the equation these AIRs force is the equation o1-labs' verifier checks.
-/

end Dregg2.Circuit.Emit.PastaMsmLayouts

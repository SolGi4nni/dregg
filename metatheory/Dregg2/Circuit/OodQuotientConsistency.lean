/-
# `Dregg2.Circuit.OodQuotientConsistency` — DEBT-A KEYSTONE: the OOD quotient-consistency
argument, and the PRECISE seam it does (and does not) close between `FriVerifier.verifyAlgo`
and `AirChecksSatisfied.MainAirAccept`.

## HONEST SCOPE (first sentence)

`verifyAlgo @ fullChecks accepts ⟹ MainAirAccept hash d t` is **NOT** provable as a single
committed term over the deployed objects, and this file says exactly why AND proves the two real
halves that flank the gap. (1) The DEPLOYED-verifier half is closed: `verifyAlgo @ fullChecks = true`
FORCES, for every opened table, the out-of-domain quotient identity `constraintEval =
vanishingAtZeta · quotientAtZeta` (`verifyAlgo_accept_forces_table_identity` — literally the
contrapositive of the committed `verifyAlgo_full_rejects_tampered_quotient`). (2) The
Schwartz–Zippel OOD half is closed over ANY integral domain: a residual polynomial `R = C − Z_H·q`
that vanishes at a NON-EXCEPTIONAL point ζ is the ZERO polynomial (`ood_consistency`), so `C`
vanishes on every root of `Z_H` — i.e. on every trace row — with the exceptional-ζ set NAMED
(`exceptionalSet R = R.roots.toFinset`, `card ≤ R.natDegree`; BabyBear soundness error
`≤ deg / 2013265921`). Running that half over ℤ lands EXACTLY the `MainAirAccept` shape
(`ood_forces_mainAirAccept`), given an interpolation bridge `OodInterpZ`.

## THE SEAM — why the two halves DO NOT compose into one term (the real structural gap)

The two proved halves live over DIFFERENT algebraic objects, and nothing in the committed tree
bridges them:

  * **Field vs. integer.** `verifyAlgo`/`TableOpening` deliver the OOD identity over BabyBear
    (`ZMod 2013265921`), a MOD-p equation on single field elements. `MainAirAccept`/`arithResidual`
    are over **ℤ** — an INTEGER per-row identity with existential ℤ `zerofier`/`quot`. The
    canonical-lift (a mod-p residual of 0 ⟹ the integer `arithResidual` is 0, needing a range
    bound on `arithResidual`) is UNMODELED. So the bridge's `OodInterpZ.hood` (a per-constraint OOD
    identity over ℤ) is what verifyAlgo WOULD supply — but verifyAlgo supplies it mod p, over the
    COMBINED constraint, not per-constraint. It is carried as an explicit premise, exactly as
    `AirChecksSatisfied.hbus` / `LogUpSoundness`'s residual are carried.
  * **Trace-column interpolation.** `arithResidual` is a raw ℤ per row; `TableOpening.constraintEval`
    is a raw field element at ζ. NEITHER exposes the trace-column-as-polynomial interpolation the OOD
    argument runs on (`OodInterpZ.hCrow` : `(Cp c).eval (rowPt i) = arithResidual … c`, and
    `OodInterpZ.hZrow` : `Z_H.eval (rowPt i) = 0`). That interpolation is the unmodeled plumbing.
  * **Constraint-batching (RLC).** `verifyAlgo` batches ALL declared constraints into ONE combined
    `constraintEval` per table via a Fiat-Shamir challenge; `MainAirAccept` wants a PER-constraint
    `quot i c`. Splitting the combined quotient back into per-constraint quotients is a SECOND
    Schwartz–Zippel step over the batching challenge — also unmodeled here.

So this file REDUCES the seam to a named, honest bridge and proves everything on both sides of it;
it does not fake a term over the deployed objects. `q`-low-degree (the FRI deliverable) enters as the
degree bound on `qp` that makes `R = C − Z_H·q` low-degree, so the exceptional set is small — it is
NOT a disguised assumption of the conclusion (the conclusion `MainAirAccept` is derived from the
polynomial IDENTITY `Cp = Zp·qp`, which `ood_consistency` PROVES from the pointwise ζ-identity).

## Teeth (both truth-values load-bearing)

  * FIRE: an honest match `C = Z_H·q` at a non-exceptional ζ gives back the identity
    (`ood_consistency_fires`), and a zero-residual interpolation yields `MainAirAccept`
    (`ood_forces_mainAirAccept_fires` — the same witness `honest_mainAirAccept` exhibits).
  * BITE: a tampered quotient (`C ≠ Z_H·q`) FAILS the OOD identity at a non-exceptional ζ
    (`ood_tamper_bites`) — the same reject direction as `verifyAlgo_full_rejects_tampered_quotient`.
  * EXCEPTIONAL ESCAPE (hnonexc is load-bearing): at an EXCEPTIONAL ζ the tampered quotient PASSES
    the pointwise identity even though `C ≠ Z_H·q` (`ood_exceptional_escape`) — the exceptional set
    is real, not vacuous.
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Degree
import Dregg2.Circuit.AirChecksSatisfied
import Dregg2.Circuit.FriVerifier
import Dregg2.Circuit.BabyBearFriField

namespace Dregg2.Circuit.OodQuotientConsistency

open Polynomial
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.AirChecksSatisfied
open Dregg2.Exec.CircuitEmit (EmittedExpr)

/-! ## §1 — The exceptional set and the Schwartz–Zippel bound (over any integral domain).

The out-of-domain point ζ is drawn by Fiat–Shamir. A residual polynomial `R` that is NONZERO (a
genuine constraint/quotient mismatch) can still evaluate to `0` at ζ only if ζ is a ROOT of `R`, and
`R` has at most `deg R` roots. That root set is the exceptional set; when `R = C − Z_H·q` is
low-degree (FRI delivers `q` low-degree, `C` low-degree by construction) the set is small relative to
`|F|`. This is the identical `card_roots'` route `LogUpSoundness` runs on the LogUp bus numerator. -/

variable {F : Type*} [CommRing F] [IsDomain F] [DecidableEq F]

/-- **The exceptional set** — the out-of-domain points at which a MISMATCHED residual can still
vanish: the roots of `R`. Named, as the honest Schwartz–Zippel form demands. -/
noncomputable def exceptionalSet (R : Polynomial F) : Finset F := R.roots.toFinset

/-- **The exceptional set is SMALL.** A nonzero residual vanishes at at most `natDegree R` points
(`Polynomial.card_roots'`). For `R = C − Z_H·q` this is `≤ deg C ⊔ (|H| + deg q)`; with `q`
FRI-low-degree the bound is a small multiple of the trace length. -/
theorem exceptionalSet_card_le (R : Polynomial F) :
    (exceptionalSet R).card ≤ R.natDegree :=
  calc (exceptionalSet R).card
      ≤ Multiset.card R.roots := Multiset.toFinset_card_le _
    _ ≤ R.natDegree := card_roots' R

/-- **The keystone lemma — a residual vanishing at a NON-EXCEPTIONAL point is the zero polynomial.**
If `R.eval ζ = 0` and ζ is not a root of `R`, then `R = 0`. (If `R ≠ 0`, `R.eval ζ = 0` puts ζ in
`R.roots ⊆ exceptionalSet R`, contradicting non-exceptionality.) This is the whole Schwartz–Zippel
content: a low-degree witness that agrees with the committed value at the random ζ agrees EVERYWHERE. -/
theorem nonexceptional_eval_zero_forces_zero (R : Polynomial F) (ζ : F)
    (hζ : R.eval ζ = 0) (hnonexc : ζ ∉ exceptionalSet R) : R = 0 := by
  by_contra hR
  exact hnonexc (by
    rw [exceptionalSet, Multiset.mem_toFinset, mem_roots hR]
    exact hζ)

/-- **`ood_consistency` — the out-of-domain quotient-consistency theorem.** The verifier checks the
quotient identity `C(ζ) = Z_H(ζ)·q(ζ)` at the Fiat–Shamir OOD point ζ. If ζ is non-exceptional for
the residual `C − Z_H·q`, that single pointwise identity forces the FULL polynomial identity
`C = Z_H·q`. Everything downstream (C vanishes on the trace rows = the roots of `Z_H`) is a
corollary of this equality of polynomials. -/
theorem ood_consistency (Cp Zp qp : Polynomial F) (ζ : F)
    (hid : Cp.eval ζ = Zp.eval ζ * qp.eval ζ)
    (hnonexc : ζ ∉ exceptionalSet (Cp - Zp * qp)) :
    Cp = Zp * qp := by
  have hζ : (Cp - Zp * qp).eval ζ = 0 := by
    rw [eval_sub, eval_mul, hid, sub_self]
  exact sub_eq_zero.mp (nonexceptional_eval_zero_forces_zero _ ζ hζ hnonexc)

omit [IsDomain F] [DecidableEq F] in
/-- **C vanishes on the trace rows.** Given the polynomial identity `C = Z_H·q` and that the trace
rows are roots of `Z_H` (the evaluation-domain geometry, recomputed by the verifier), `C` vanishes at
every trace row — the per-row constraint identity the AIR asserts. -/
theorem ood_forces_row_vanish (Cp Zp qp : Polynomial F) (pts : List F)
    (hCq : Cp = Zp * qp) (hZ : ∀ x ∈ pts, Zp.eval x = 0) :
    ∀ x ∈ pts, Cp.eval x = 0 := by
  intro x hx
  rw [hCq, eval_mul, hZ x hx, zero_mul]

/-! ## §2 — The DEPLOYED-verifier half: acceptance FORCES the OOD identity (per opened table).

This is the exact contrapositive of the committed `FriVerifier.verifyAlgo_full_rejects_tampered_quotient`
(`FriVerifier.lean:752`, which proves a TAMPERED quotient at ζ makes the full verifier REJECT). No
separate work is needed: `by_contra` hands us the tamper hypothesis, the committed theorem rejects,
contradicting acceptance. This connects the deployed verifier's Boolean verdict to the pointwise
ζ-identity that `ood_consistency` consumes. -/

open Dregg2.Circuit.FriVerifier

/-- **`verifyAlgo @ fullChecks accepts ⟹ the OOD quotient identity holds at every opened table.**
For each `topen ∈ proof.tableOpenings`, acceptance forces `constraintEval = A.mul vanishingAtZeta
quotientAtZeta` — the mod-`|F|` image of `C(ζ) = Z_H(ζ)·q(ζ)`. (Contrapositive of the committed
reject tooth; the answer to DEBT-A DO-step 1: the acceptance direction IS that contrapositive.) -/
theorem verifyAlgo_accept_forces_table_identity {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat)
    (params : FriParams) (vk : RecursionVk F) (core : FriCore F) (A : FieldArith F)
    (initState : List F) (logN : Nat) (proof : BatchProofData F) (pub : WrapPublics F)
    (ood : F) (hood : proof.oodPoint = [ood])
    (topen : TableOpening F) (hmem : topen ∈ proof.tableOpenings)
    (h : verifyAlgo perm RATE toNat params vk (fullChecks core A toNat params.powBits)
          initState logN proof pub = true) :
    topen.constraintEval = A.mul topen.vanishingAtZeta topen.quotientAtZeta := by
  by_contra hne
  have hrej := verifyAlgo_full_rejects_tampered_quotient perm RATE toNat params vk core A
    initState logN proof pub ood hood topen hmem hne
  rw [hrej] at h
  exact absurd h (by decide)

/-! ## §3 — The Schwartz–Zippel half, landed on the `MainAirAccept` shape (over ℤ).

`MainAirAccept` is an INTEGER per-row statement (`arithResidual … c = zerofier i · quot i c`,
`zerofier i = 0` on rows). ℤ is an integral domain, so the SAME `ood_consistency` runs over ℤ[X].
The `OodInterpZ` bridge carries the interpolation that neither `TableOpening` nor `MainAirAccept`
exposes (see the seam discussion in the header). Given it, the OOD argument produces `MainAirAccept`
with `zerofier i := Z_H.eval (rowPt i)` and `quot i c := q_c.eval (rowPt i)` — genuine ℤ witnesses. -/

/-- **The interpolation bridge (the honest, named residual).** For a descriptor `d` and trace `t`,
this packages the UNMODELED trace-column-as-polynomial interpolation over ℤ. It carries NEITHER
`MainAirAccept` nor the polynomial identity `Cp = Zp·qp` — only (i) the pointwise OOD identity at ζ
(what `verifyAlgo` would deliver, modulo the field/integer + RLC gaps), (ii) that ζ is
non-exceptional (Fiat–Shamir), (iii) the interpolation of the per-row residual, and (iv) that trace
rows are roots of the vanishing polynomial. The polynomial identity is DERIVED by `ood_consistency`. -/
structure OodInterpZ (d : EffectVmDescriptor2) (t : VmTrace) where
  /-- The Fiat–Shamir out-of-domain point (over ℤ; the deployed one is mod `|F|` — the field/integer
  gap). -/
  ζ : ℤ
  /-- The trace-domain embedding of row `i` (the `H`-coset point; unmodeled). -/
  rowPt : ℕ → ℤ
  /-- The vanishing polynomial `Z_H` (unmodeled). -/
  Zp : Polynomial ℤ
  /-- The per-constraint constraint-composition polynomial `C_c` (interpolation of the trace columns
  through the gate; unmodeled). -/
  Cp : VmConstraint2 → Polynomial ℤ
  /-- The per-constraint committed quotient `q_c`; FRI delivers its LOW DEGREE (the reason `Cp − Zp·qp`
  is low-degree, hence the exceptional set is small). -/
  qp : VmConstraint2 → Polynomial ℤ
  /-- **Interpolation.** The composition polynomial reproduces the per-row residual at the row point.
  This is the raw-ℤ-`arithResidual`-to-polynomial bridge that is UNMODELED in the tree. -/
  hCrow : ∀ i, ∀ c ∈ d.constraints,
      (Cp c).eval (rowPt i) = arithResidual (envAt t i) (i == 0) (i + 1 == t.rows.length) c
  /-- **Domain geometry.** Trace rows are roots of `Z_H` (recomputed by the verifier, not trusted). -/
  hZrow : ∀ i < t.rows.length, (Zp).eval (rowPt i) = 0
  /-- **The OOD quotient identity at ζ, per constraint** (the image of `verifyAlgo`'s `tableOk`; over
  the COMBINED constraint and mod `|F|` in deployment — the RLC + field/integer residuals). -/
  hood : ∀ c ∈ d.constraints, (Cp c).eval ζ = (Zp).eval ζ * (qp c).eval ζ
  /-- **ζ is non-exceptional** for each per-constraint residual (Fiat–Shamir; the escape probability
  is bounded by `exceptionalSet_card_le`). -/
  hnonexc : ∀ c ∈ d.constraints, ζ ∉ exceptionalSet ((Cp c) - (Zp) * (qp c))

/-- **`ood_forces_mainAirAccept` — the Schwartz–Zippel half lands the `MainAirAccept` shape.** Under
the interpolation bridge, `verifyAlgo`'s OOD identity (carried by `hood`) plus non-exceptionality
force, PER CONSTRAINT, the polynomial identity `Cp c = Zp·qp c` (by `ood_consistency`); the row
interpolation then reads off `MainAirAccept` with `zerofier := Z_H.eval ∘ rowPt`, `quot := qp ∘ rowPt`.
The load-bearing NEW step is `ood_consistency`; the bridge supplies only the ζ-pointwise identity and
the interpolation, never the polynomial identity itself. -/
theorem ood_forces_mainAirAccept (hash : List ℤ → ℤ) (d : EffectVmDescriptor2) (t : VmTrace)
    (I : OodInterpZ d t) : MainAirAccept hash d t := by
  refine ⟨fun i c => (I.qp c).eval (I.rowPt i), fun i => (I.Zp).eval (I.rowPt i), ?_, ?_⟩
  · intro i c hc
    have hCq : I.Cp c = I.Zp * I.qp c :=
      ood_consistency (I.Cp c) I.Zp (I.qp c) I.ζ (I.hood c hc) (I.hnonexc c hc)
    rw [← I.hCrow i c hc, hCq, eval_mul]
  · intro i hi
    exact I.hZrow i hi

/-! ## §4 — BabyBear soundness error (the concrete Schwartz–Zippel bound). -/

section BabyBear
open Dregg2.Circuit.BabyBearFriField

/-- **The OOD soundness error at BabyBear.** A nonzero residual `R = C − Z_H·q` vanishes at at most
`natDegree R` of the `|F| = 2013265921` out-of-domain points, so a uniform ζ catches a tampered
quotient except with probability `≤ natDegree R / 2013265921`. Concrete Schwartz–Zippel bound over the
DEPLOYED field (not `ZMod 5`). -/
theorem babybear_ood_soundness_error (R : Polynomial BabyBear) :
    (exceptionalSet R).card ≤ R.natDegree ∧ Fintype.card BabyBear = 2013265921 :=
  ⟨exceptionalSet_card_le R, by
    haveI : NeZero babyBearP := ⟨by norm_num⟩
    exact ZMod.card babyBearP⟩

end BabyBear

/-! ## §5 — TEETH (both truth-values load-bearing), over ℤ. -/

section Teeth

/-- FIRE: an honest match `C = Z_H·q` — here `Cp = X·3`, `Zp = X`, `qp = 3` — satisfies the pointwise
OOD identity at the non-exceptional ζ = 5, and `ood_consistency` returns the polynomial identity. The
residual `Cp − Zp·qp = 0` has empty exceptional set, so ζ = 5 is non-exceptional. -/
theorem ood_consistency_fires :
    (X * C (3 : ℤ)) = (X : Polynomial ℤ) * C 3 := by
  apply ood_consistency (X * C (3 : ℤ)) X (C 3) 5
  · simp
  · simp [exceptionalSet]

/-- BITE: a tampered quotient — `Cp = X`, `Zp = X`, `qp = 2`, so `Cp ≠ Zp·qp = 2X` — FAILS the
pointwise OOD identity at the non-exceptional ζ = 5 (`5 ≠ 5·2`). A prover cannot forge the quotient
and pass the OOD check off the exceptional set (the same reject as the committed verifier tooth). -/
theorem ood_tamper_bites :
    (X : Polynomial ℤ).eval 5 ≠ (X : Polynomial ℤ).eval 5 * (C (2 : ℤ)).eval 5 := by
  rw [eval_X, eval_C]; norm_num

/-- EXCEPTIONAL ESCAPE (proves `hnonexc` is load-bearing): at the EXCEPTIONAL point ζ = 0 the SAME
tampered quotient (`X ≠ X·2`) DOES satisfy the pointwise identity (`0 = 0·2`). Without demanding ζ
non-exceptional, `ood_consistency` would be FALSE — the exceptional set is genuinely non-vacuous. -/
theorem ood_exceptional_escape :
    ((X : Polynomial ℤ).eval 0 = (X : Polynomial ℤ).eval 0 * (C (2 : ℤ)).eval 0)
      ∧ (X : Polynomial ℤ) ≠ X * C 2 := by
  refine ⟨by simp, ?_⟩
  intro h
  have := congrArg (Polynomial.eval (1 : ℤ)) h
  rw [eval_X, eval_mul, eval_X, eval_C] at this
  norm_num at this

/-- FIRE, all the way to `MainAirAccept`: the zero interpolation (`Cp = Zp = qp = 0`, `rowPt = id`)
over the committed honest toy trace `AirChecksSatisfied.tHonest` yields an `OodInterpZ`, so
`ood_forces_mainAirAccept` produces the SAME `MainAirAccept` the committed `honest_mainAirAccept`
exhibits — the landing theorem is not vacuous. -/
theorem ood_forces_mainAirAccept_fires :
    MainAirAccept (fun _ => 0) dArith tHonest :=
  ood_forces_mainAirAccept (fun _ => 0) dArith tHonest
    { ζ := 5
    , rowPt := fun _ => 0
    , Zp := 0
    , Cp := fun _ => 0
    , qp := fun _ => 0
    , hCrow := by
        intro i c hc
        simp only [dArith, List.mem_singleton] at hc
        subst hc
        rw [eval_zero]
        -- arithResidual of `.base (.gate (.var 0))` is 0 at every i on the honest all-zero trace.
        rcases i with _ | _ | i
        · rfl
        · rfl
        · simp [arithResidual, envAt, tHonest, EmittedExpr.eval, List.getD, zeroAsg]
    , hZrow := by intro i _; rw [eval_zero]
    , hood := by intro c _; rw [eval_zero]; ring
    , hnonexc := by intro c _; simp [exceptionalSet] }

end Teeth

#assert_axioms exceptionalSet_card_le
#assert_axioms nonexceptional_eval_zero_forces_zero
#assert_axioms ood_consistency
#assert_axioms ood_forces_row_vanish
#assert_axioms verifyAlgo_accept_forces_table_identity
#assert_axioms ood_forces_mainAirAccept
#assert_axioms babybear_ood_soundness_error
#assert_axioms ood_consistency_fires
#assert_axioms ood_tamper_bites
#assert_axioms ood_exceptional_escape
#assert_axioms ood_forces_mainAirAccept_fires

#check @ood_consistency
#check @verifyAlgo_accept_forces_table_identity
#check @ood_forces_mainAirAccept

end Dregg2.Circuit.OodQuotientConsistency

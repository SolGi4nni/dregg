/-
# Dregg2.Circuit.Emit.QuantifiedAbsenceRefine — the WHOLE-DESCRIPTOR functional-refinement bridge for
the `quantified_absence` family (Approach B: the certified-complement quotient accumulator).

## What Rung-0 already gave, and what this file adds

`QuantifiedAbsenceEmit.lean` byte-pins the descriptor `quantifiedAbsenceDesc` and proves the per-GATE
teeth (`diffBody0_zero_iff`, `prodBody0_zero_iff`, `sumBody0_zero_iff` — each a single limb's gate poly
= 0 ↔ its LOCAL relation). What was MISSING is the whole-descriptor bridge: that an assignment/trace
which SATISFIES the descriptor (`DescriptorIR2.Satisfied2`) corresponds to the GENUINE semantic relation
the circuit computes — the polynomial-division / accumulator-quotient identity over BabyBear⁴.

## The semantic relation (the NO-emit-model half — we AUTHOR the functional spec)

The dossier's `lean_spec` names `Authority.QuantifiedPredicate` (the guard-language ∀/∃ fragment over
cleartext records) and `Circuit.SortedTreeNonMembershipHeap8` (the sorted-tree non-membership route).
NEITHER is the relation THIS descriptor (Approach B) computes: the deployed `QuotientAccumulatorAir`
(`quantified_absence.rs:438`) enforces, over BabyBear⁴ (the extension `X⁴ − 11`), the division certificate

    w ⊗ (α ⊖ elem) ⊕ v  =  Acc_all

by materializing `diff = α ⊖ elem`, `prod = w ⊗ diff`, `sum = prod ⊕ v` and pinning `sum = Acc_all`, with
`α` the public challenge. So we FIRST author that relation as a clean Lean functional spec
(`QuotientAbsenceRel`, over the BabyBear⁴ extension ops `extAdd`/`extSub`/`extMul` that mirror
`ExtElem::mul` mod `X⁴ − 11`) and THEN prove the descriptor REFINES it: `Satisfied2 ⟹ QuotientAbsenceRel`.

## Honest scope (unchanged from the emit file, §"THE OFF-DESCRIPTOR CARRIER")

Like the hand AIR, this bridge concludes ONLY the arithmetic quotient identity over the witness-supplied
`(elem, w, v)` bound to the public `(Acc_all, α)`. It does NOT re-derive that `Acc_all` is a genuine
product `∏(α − hᵢ)` or that `v` is the honest cofactor — those stay the executor-verified / witnessed
carriers of the family (the deployed AIR does not check them either). This is the faithful functional
refinement of what the emitted descriptor DOES enforce, not a soundness upgrade of the family.

## The load-bearing direction + non-vacuity

`quantifiedAbsence_refines` is SAT_IMPLIES_SEM: accept ⟹ the genuine relation holds on the active row.
The hypothesis is NOT hollow: `quantifiedAbsence_sat` exhibits a CONCRETE 2-row trace that genuinely
satisfies `Satisfied2` (all nine legs), and `quantifiedAbsence_bad` a concrete trace that FAILS it (the
`sum = Acc_all` pin bites). `quantifiedAbsence_sat_relation` composes the two: the honest witness is
carried through the bridge to a concrete instance of `QuotientAbsenceRel`, whose two `decide` bits
(true on `(8,0,0,0)`, false on `(9,0,0,0)`) show the relation genuinely discriminates.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. No hashing / chip / map-op carrier enters —
the descriptor declares NO tables, hash sites, ranges, or mem/map ops (`tables=[] hashSites=[] ranges=[]`),
so the bridge is pure base-gate + PI-binding algebra. NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.QuantifiedAbsenceEmit
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.DecideSatisfied2

namespace Dregg2.Circuit.Emit.QuantifiedAbsenceRefine

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit
  (VmConstraint VmRow VmRowEnv holdsVm_gate_false holdsVm_piFirst_true)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Satisfied2 VmTrace envAt zeroAsg memLog mapLog)
open Dregg2.Circuit.Argus.InterpCore (decideConstraint decideConstraint_iff)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff)
open Dregg2.Circuit.Emit.QuantifiedAbsenceEmit

set_option autoImplicit false

/-! ## §0 — field-denotation glue. The DEPLOYED `VmConstraint.holdsVm` pins every gate/PI only
`≡ 0 [ZMOD p]` / `≡ pub [ZMOD p]` (`p` the BabyBear prime), NOT `= 0` over ℤ. For the BabyBear⁴
quotient certificate the extension MULTIPLICATION `w ⊗ diff` is a genuine field product (its ℤ value
overflows the canonical window, so no range-check can lift it to an ℤ identity) — so the faithful
semantics is the field relation, stated `≡ [ZMOD p]` per limb (the same convention the deployed
`ExtElem::mul` computes, and that green `EffectActionBindingRefine`/`GarbledEvalRefine` use). The two
glue lemmas move a mod-`p` congruence into `ZMod p` (a `CommRing`, where `ring`/`rw` discharge the
whole extension-field algebra) and back. -/

/-- A mod-`p` congruence IS an equality of the two integers cast into `ZMod p`. -/
theorem toZMod {a b : ℤ} (h : a ≡ b [ZMOD 2013265921]) :
    (a : ZMod 2013265921) = (b : ZMod 2013265921) := by
  rwa [ZMod.intCast_eq_intCast_iff]

/-- …and conversely: equality in `ZMod p` recovers the mod-`p` congruence. -/
theorem ofZMod {a b : ℤ} (h : (a : ZMod 2013265921) = (b : ZMod 2013265921)) :
    a ≡ b [ZMOD 2013265921] := by
  rwa [ZMod.intCast_eq_intCast_iff] at h

/-! ## §1 — The semantic relation: the BabyBear⁴ quotient-division certificate (the authored spec). -/

/-- A BabyBear⁴ extension element, in limb coordinates over the basis `(1, X, X², X³)` with `X⁴ = 11`
(the `ExtElem` layout of `accumulator_types.rs`). -/
abbrev Ext : Type := ℤ × ℤ × ℤ × ℤ

/-- Extension subtraction (componentwise) — the `diff = α − elem` step. -/
def extSub : Ext → Ext → Ext
  | (a0, a1, a2, a3), (b0, b1, b2, b3) => (a0 - b0, a1 - b1, a2 - b2, a3 - b3)

/-- Extension addition (componentwise) — the `sum = prod + v` step. -/
def extAdd : Ext → Ext → Ext
  | (a0, a1, a2, a3), (b0, b1, b2, b3) => (a0 + b0, a1 + b1, a2 + b2, a3 + b3)

/-- Extension multiplication mod `X⁴ − 11` — the four output limbs are `ExtElem::mul`
(`accumulator_types.rs:93`) term-for-term, and are EXACTLY the descriptor's `prodC0..prodC3` gate
bodies. This is the `prod = w · diff` step. -/
def extMul : Ext → Ext → Ext
  | (q0, q1, q2, q3), (d0, d1, d2, d3) =>
    ( q0 * d0 + 11 * (q1 * d3 + q2 * d2 + q3 * d1)
    , q0 * d1 + q1 * d0 + 11 * (q2 * d3 + q3 * d2)
    , q0 * d2 + q1 * d1 + q2 * d0 + 11 * (q3 * d3)
    , q0 * d3 + q1 * d2 + q2 * d1 + q3 * d0 )

/-- **`QuotientAbsenceRel elem w v accAll alpha`** — the genuine functional spec the quotient-accumulator
circuit computes over BabyBear⁴: the witness `(elem, w, v)` is a polynomial-division certificate binding
the public accumulator value `accAll` at the challenge `alpha`:

    w ⊗ (alpha ⊖ elem) ⊕ v  =  accAll   (as elements of 𝔽_p⁴, i.e. per limb `≡ [ZMOD p]`).

The equality is stated per limb over the BabyBear field `𝔽_p` (`≡ [ZMOD p]`) — the FAITHFUL semantics
of the deployed field circuit: `ExtElem::mul` reduces mod `p`, and the extension product overflows the
canonical ℤ window, so no ℤ identity is enforced. (For the intended semantics, `accAll` is the
characteristic value `∏(alpha − hᵢ)` of the satisfying set; this relation is the quotient-with-remainder
certificate against the factor `(alpha − elem)`.) -/
def QuotientAbsenceRel (elem w v accAll alpha : Ext) : Prop :=
  match extAdd (extMul w (extSub alpha elem)) v, accAll with
  | (r0, r1, r2, r3), (a0, a1, a2, a3) =>
      r0 ≡ a0 [ZMOD 2013265921] ∧ r1 ≡ a1 [ZMOD 2013265921]
      ∧ r2 ≡ a2 [ZMOD 2013265921] ∧ r3 ≡ a3 [ZMOD 2013265921]

/-! ## §2 — Membership of each constraint group into the whole descriptor's constraint list.
`quantifiedAbsenceDesc.constraints = diffGates ++ prodGates ++ sumGates ++ sumPins ++ alphaPins`. -/

theorem mem_of_diff {c : VmConstraint2} (hc : c ∈ diffGates) :
    c ∈ quantifiedAbsenceDesc.constraints := by
  show c ∈ diffGates ++ prodGates ++ sumGates ++ sumPins ++ alphaPins
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (List.mem_append.mpr
    (Or.inl (List.mem_append.mpr (Or.inl hc)))))))

theorem mem_of_prod {c : VmConstraint2} (hc : c ∈ prodGates) :
    c ∈ quantifiedAbsenceDesc.constraints := by
  show c ∈ diffGates ++ prodGates ++ sumGates ++ sumPins ++ alphaPins
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (List.mem_append.mpr
    (Or.inl (List.mem_append.mpr (Or.inr hc)))))))

theorem mem_of_sum {c : VmConstraint2} (hc : c ∈ sumGates) :
    c ∈ quantifiedAbsenceDesc.constraints := by
  show c ∈ diffGates ++ prodGates ++ sumGates ++ sumPins ++ alphaPins
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hc)))))

theorem mem_of_sumPin {c : VmConstraint2} (hc : c ∈ sumPins) :
    c ∈ quantifiedAbsenceDesc.constraints := by
  show c ∈ diffGates ++ prodGates ++ sumGates ++ sumPins ++ alphaPins
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hc)))

theorem mem_of_alphaPin {c : VmConstraint2} (hc : c ∈ alphaPins) :
    c ∈ quantifiedAbsenceDesc.constraints := by
  show c ∈ diffGates ++ prodGates ++ sumGates ++ sumPins ++ alphaPins
  exact List.mem_append.mpr (Or.inr hc)

/-! ## §3 — Row-0 extraction: on an ACTIVE (≥ 2 rows, non-last) first row, each declared gate body
vanishes and each first-row PI binding holds. (Row 0 of a ≥2-row trace is BOTH `isFirst` and a
transition row, so gates fire under `when_transition` and PI pins fire under `when_first_row`.) -/

section Bridge

variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- A declared `.gate body` forces `body.eval ≡ 0 [ZMOD p]` on the active first row (the DEPLOYED
field constraint). -/
theorem gate_holds0
    (h : Satisfied2 hash quantifiedAbsenceDesc minit mfin maddrs t) (h2 : 2 ≤ t.rows.length)
    (body : EmittedExpr)
    (hin : VmConstraint2.base (.gate body) ∈ quantifiedAbsenceDesc.constraints) :
    body.eval (envAt t 0).loc ≡ 0 [ZMOD 2013265921] := by
  have hlen : 0 < t.rows.length := by omega
  have hlast : (0 + 1 == t.rows.length) = false := by rw [beq_eq_false_iff_ne]; omega
  have g := h.rowConstraints 0 hlen _ hin
  simp only [VmConstraint2.holdsAt, hlast, holdsVm_gate_false] at g
  exact g

/-- A declared first-row `.piBinding` forces `loc col ≡ pub k [ZMOD p]` on the active first row. -/
theorem pin_holds0
    (h : Satisfied2 hash quantifiedAbsenceDesc minit mfin maddrs t) (h2 : 2 ≤ t.rows.length)
    (col k : Nat)
    (hin : VmConstraint2.base (.piBinding .first col k) ∈ quantifiedAbsenceDesc.constraints) :
    (envAt t 0).loc col ≡ (envAt t 0).pub k [ZMOD 2013265921] := by
  have hlen : 0 < t.rows.length := by omega
  have g := h.rowConstraints 0 hlen _ hin
  simp only [VmConstraint2.holdsAt, show (0 == 0) = true from rfl, holdsVm_piFirst_true] at g
  exact g

/-! ## §4 — THE WHOLE-DESCRIPTOR BRIDGE: `Satisfied2 ⟹ QuotientAbsenceRel`. -/

/-- **`quantifiedAbsence_refines` — THE BRIDGE (SAT_IMPLIES_SEM).** Any multi-table witness that
SATISFIES the whole quotient-accumulator descriptor (on a ≥2-row trace, so row 0 is an active
transition row) realizes the genuine BabyBear⁴ division certificate on that row: the witness columns
`(elem, w, v)` and the public `(Acc_all, α)` satisfy `w ⊗ (α ⊖ elem) ⊕ v = Acc_all`. This composes the
whole constraint set — the four diff gates, the four `X⁴−11` product gates, the four sum gates, and the
eight PI pins (`sum = Acc_all`, `α` materialized) — into the extension-field relation, NOT a single
gate's tooth. -/
theorem quantifiedAbsence_refines
    (h : Satisfied2 hash quantifiedAbsenceDesc minit mfin maddrs t) (h2 : 2 ≤ t.rows.length) :
    QuotientAbsenceRel
      ((envAt t 0).loc E0, (envAt t 0).loc E1, (envAt t 0).loc E2, (envAt t 0).loc E3)   -- elem
      ((envAt t 0).loc Q0, (envAt t 0).loc Q1, (envAt t 0).loc Q2, (envAt t 0).loc Q3)   -- w
      ((envAt t 0).loc V0, (envAt t 0).loc V1, (envAt t 0).loc V2, (envAt t 0).loc V3)   -- v
      ((envAt t 0).pub (PI_ACC0 + 0), (envAt t 0).pub (PI_ACC0 + 1),
       (envAt t 0).pub (PI_ACC0 + 2), (envAt t 0).pub (PI_ACC0 + 3))                     -- Acc_all
      ((envAt t 0).pub (PI_ALPHA0 + 0), (envAt t 0).pub (PI_ALPHA0 + 1),
       (envAt t 0).pub (PI_ALPHA0 + 2), (envAt t 0).pub (PI_ALPHA0 + 3)) := by            -- α
  -- α materialization: the ALPHA columns carry the α public challenge (mod-`p`).
  have gA0 := pin_holds0 h h2 A0 (PI_ALPHA0 + 0) (mem_of_alphaPin (List.mem_cons.mpr (Or.inl rfl)))
  have gA1 := pin_holds0 h h2 A1 (PI_ALPHA0 + 1)
    (mem_of_alphaPin (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))
  have gA2 := pin_holds0 h h2 A2 (PI_ALPHA0 + 2)
    (mem_of_alphaPin (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))
  have gA3 := pin_holds0 h h2 A3 (PI_ALPHA0 + 3)
    (mem_of_alphaPin (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))
  -- diff gates ⟹ `diff ≡ α_col − elem [ZMOD p]` (per limb; α_col substituted to the PI below).
  have hD0 : (envAt t 0).loc D0 ≡ (envAt t 0).loc A0 - (envAt t 0).loc E0 [ZMOD 2013265921] :=
    (gate_modEq_iff (by simp only [diffBody, subCols, EmittedExpr.eval]; ring)).mp
      (gate_holds0 h h2 (diffBody D0 A0 E0) (mem_of_diff (List.mem_cons.mpr (Or.inl rfl))))
  have hD1 : (envAt t 0).loc D1 ≡ (envAt t 0).loc A1 - (envAt t 0).loc E1 [ZMOD 2013265921] :=
    (gate_modEq_iff (by simp only [diffBody, subCols, EmittedExpr.eval]; ring)).mp
      (gate_holds0 h h2 (diffBody D1 A1 E1)
        (mem_of_diff (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))
  have hD2 : (envAt t 0).loc D2 ≡ (envAt t 0).loc A2 - (envAt t 0).loc E2 [ZMOD 2013265921] :=
    (gate_modEq_iff (by simp only [diffBody, subCols, EmittedExpr.eval]; ring)).mp
      (gate_holds0 h h2 (diffBody D2 A2 E2)
        (mem_of_diff (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))
  have hD3 : (envAt t 0).loc D3 ≡ (envAt t 0).loc A3 - (envAt t 0).loc E3 [ZMOD 2013265921] :=
    (gate_modEq_iff (by simp only [diffBody, subCols, EmittedExpr.eval]; ring)).mp
      (gate_holds0 h h2 (diffBody D3 A3 E3)
        (mem_of_diff (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))
  -- product gates ⟹ `prod ≡ w ⊗ diff [ZMOD p]` (per limb; the `X⁴−11` bilinear form).
  have hP0 : (envAt t 0).loc P0 ≡ (envAt t 0).loc Q0 * (envAt t 0).loc D0
      + 11 * ((envAt t 0).loc Q1 * (envAt t 0).loc D3 + (envAt t 0).loc Q2 * (envAt t 0).loc D2
              + (envAt t 0).loc Q3 * (envAt t 0).loc D1) [ZMOD 2013265921] :=
    (gate_modEq_iff (by simp only [prodBody, prodC0, vv, w11, EmittedExpr.eval]; ring)).mp
      (gate_holds0 h h2 (prodBody P0 prodC0) (mem_of_prod (List.mem_cons.mpr (Or.inl rfl))))
  have hP1' : (envAt t 0).loc P1 ≡ (envAt t 0).loc Q0 * (envAt t 0).loc D1
      + (envAt t 0).loc Q1 * (envAt t 0).loc D0
      + 11 * ((envAt t 0).loc Q2 * (envAt t 0).loc D3 + (envAt t 0).loc Q3 * (envAt t 0).loc D2)
      [ZMOD 2013265921] :=
    (gate_modEq_iff (by simp only [prodBody, prodC1, vv, w11, EmittedExpr.eval]; ring)).mp
      (gate_holds0 h h2 (prodBody P1 prodC1)
        (mem_of_prod (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))
  have hP2' : (envAt t 0).loc P2 ≡ (envAt t 0).loc Q0 * (envAt t 0).loc D2
      + (envAt t 0).loc Q1 * (envAt t 0).loc D1 + (envAt t 0).loc Q2 * (envAt t 0).loc D0
      + 11 * ((envAt t 0).loc Q3 * (envAt t 0).loc D3) [ZMOD 2013265921] :=
    (gate_modEq_iff (by simp only [prodBody, prodC2, vv, w11, EmittedExpr.eval]; ring)).mp
      (gate_holds0 h h2 (prodBody P2 prodC2)
        (mem_of_prod (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))
  have hP3' : (envAt t 0).loc P3 ≡ (envAt t 0).loc Q0 * (envAt t 0).loc D3
      + (envAt t 0).loc Q1 * (envAt t 0).loc D2 + (envAt t 0).loc Q2 * (envAt t 0).loc D1
      + (envAt t 0).loc Q3 * (envAt t 0).loc D0 [ZMOD 2013265921] :=
    (gate_modEq_iff (by simp only [prodBody, prodC3, vv, EmittedExpr.eval]; ring)).mp
      (gate_holds0 h h2 (prodBody P3 prodC3)
        (mem_of_prod (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))
  -- sum gates ⟹ `sum ≡ prod + v [ZMOD p]` (per limb).
  have hS0 : (envAt t 0).loc S0 ≡ (envAt t 0).loc P0 + (envAt t 0).loc V0 [ZMOD 2013265921] :=
    (gate_modEq_iff (by simp only [sumBody, subCols, EmittedExpr.eval]; ring)).mp
      (gate_holds0 h h2 (sumBody S0 P0 V0) (mem_of_sum (List.mem_cons.mpr (Or.inl rfl))))
  have hS1 : (envAt t 0).loc S1 ≡ (envAt t 0).loc P1 + (envAt t 0).loc V1 [ZMOD 2013265921] :=
    (gate_modEq_iff (by simp only [sumBody, subCols, EmittedExpr.eval]; ring)).mp
      (gate_holds0 h h2 (sumBody S1 P1 V1)
        (mem_of_sum (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))
  have hS2 : (envAt t 0).loc S2 ≡ (envAt t 0).loc P2 + (envAt t 0).loc V2 [ZMOD 2013265921] :=
    (gate_modEq_iff (by simp only [sumBody, subCols, EmittedExpr.eval]; ring)).mp
      (gate_holds0 h h2 (sumBody S2 P2 V2)
        (mem_of_sum (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))
  have hS3 : (envAt t 0).loc S3 ≡ (envAt t 0).loc P3 + (envAt t 0).loc V3 [ZMOD 2013265921] :=
    (gate_modEq_iff (by simp only [sumBody, subCols, EmittedExpr.eval]; ring)).mp
      (gate_holds0 h h2 (sumBody S3 P3 V3)
        (mem_of_sum (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))
  -- boundary: `sum ≡ Acc_all [ZMOD p]` (the four SUM pins to the accumulator public inputs).
  have hC0 := pin_holds0 h h2 S0 (PI_ACC0 + 0) (mem_of_sumPin (List.mem_cons.mpr (Or.inl rfl)))
  have hC1 := pin_holds0 h h2 S1 (PI_ACC0 + 1)
    (mem_of_sumPin (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))
  have hC2 := pin_holds0 h h2 S2 (PI_ACC0 + 2)
    (mem_of_sumPin (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))
  have hC3 := pin_holds0 h h2 S3 (PI_ACC0 + 3)
    (mem_of_sumPin (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))
  -- cast every mod-`p` fact into `ZMod p` (a `CommRing`), substituting α_col → PI and diff → α−elem,
  -- so the four limbs close by ring algebra.
  have zA0 := toZMod gA0; have zA1 := toZMod gA1; have zA2 := toZMod gA2; have zA3 := toZMod gA3
  have zD0 := toZMod hD0; push_cast at zD0; rw [zA0] at zD0
  have zD1 := toZMod hD1; push_cast at zD1; rw [zA1] at zD1
  have zD2 := toZMod hD2; push_cast at zD2; rw [zA2] at zD2
  have zD3 := toZMod hD3; push_cast at zD3; rw [zA3] at zD3
  have zP0 := toZMod hP0; push_cast at zP0
  have zP1 := toZMod hP1'; push_cast at zP1
  have zP2 := toZMod hP2'; push_cast at zP2
  have zP3 := toZMod hP3'; push_cast at zP3
  have zS0 := toZMod hS0; push_cast at zS0
  have zS1 := toZMod hS1; push_cast at zS1
  have zS2 := toZMod hS2; push_cast at zS2
  have zS3 := toZMod hS3; push_cast at zS3
  have zC0 := toZMod hC0; have zC1 := toZMod hC1; have zC2 := toZMod hC2; have zC3 := toZMod hC3
  -- assemble the four limbs into the extension-field identity (in `ZMod p`).
  simp only [QuotientAbsenceRel, extSub, extMul, extAdd]
  refine ⟨ofZMod ?_, ofZMod ?_, ofZMod ?_, ofZMod ?_⟩
  · push_cast; rw [← zC0, zS0, zP0, zD0, zD1, zD2, zD3]
  · push_cast; rw [← zC1, zS1, zP1, zD0, zD1, zD2, zD3]
  · push_cast; rw [← zC2, zS2, zP2, zD0, zD1, zD2, zD3]
  · push_cast; rw [← zC3, zS3, zP3, zD0, zD1, zD2, zD3]

end Bridge

/-! ## §5 — NON-VACUITY: a concrete trace that SATISFIES the descriptor, and one that FAILS it.

The satisfying witness carries one element `elem = 1`, challenge `α = 2`, quotient `w = 3`, remainder
`v = 5`, so `w·(α−elem) + v = 3·1 + 5 = 8 = Acc_all` — all in limb 0, the other limbs zero. -/

/-- Row 0 of the satisfying witness: 28 base columns, the consistent quotient trace above (else 0). -/
def satRow0 : Assignment := fun n =>
  [1,0,0,0, 3,0,0,0, 5,0,0,0, 1,0,0,0, 3,0,0,0, 8,0,0,0, 2,0,0,0].getD n 0

/-- Public inputs of the satisfying witness: `Acc_all = 8`, `α = 2` (limb 0), rest 0. -/
def satPub : Assignment := fun n => [8,0,0,0, 2,0,0,0].getD n 0

/-- The satisfying 2-row trace (row 0 active + one wrap row); no auxiliary tables. -/
def satTrace : VmTrace := { rows := [satRow0, zeroAsg], pub := satPub, tf := fun _ => [] }

/-- The memory / map logs are empty (the descriptor declares no mem/map ops). -/
theorem satTrace_memLog : memLog quantifiedAbsenceDesc satTrace = [] := by
  simp [memLog, Dregg2.Circuit.DescriptorIR2.memOpsOf, quantifiedAbsenceDesc,
    diffGates, prodGates, sumGates, sumPins, alphaPins]

theorem satTrace_mapLog : mapLog quantifiedAbsenceDesc satTrace = [] := by
  simp [mapLog, Dregg2.Circuit.DescriptorIR2.mapOpsOf, quantifiedAbsenceDesc,
    diffGates, prodGates, sumGates, sumPins, alphaPins]

/-- **`quantifiedAbsence_sat` — the hypothesis is GENUINELY INHABITED.** The concrete 2-row `satTrace`
satisfies the WHOLE deployed denotation `Satisfied2` — all nine legs, for any abstract `hash` (the
descriptor uses none). This is the concrete satisfying assignment the SAT_IMPLIES_SEM bridge consumes. -/
theorem quantifiedAbsence_sat (hash : List ℤ → ℤ) :
    Satisfied2 hash quantifiedAbsenceDesc (fun _ => 0) (fun _ => (0, 0)) [] satTrace := by
  refine
    { rowConstraints := ?_, rowHashes := ?_, rowRanges := ?_, memAddrsNodup := ?_,
      memClosed := ?_, memDisciplined := ?_, memBalanced := ?_, memTableFaithful := ?_,
      mapTableFaithful := ?_ }
  · intro i hi c hc
    simp only [quantifiedAbsenceDesc, diffGates, prodGates, sumGates, sumPins, alphaPins,
      List.cons_append, List.nil_append] at hc
    have hlen : satTrace.rows.length = 2 := rfl
    rw [hlen] at hi
    interval_cases i <;>
      (fin_cases hc <;>
        (simp only [VmConstraint2.holdsAt]; exact (decideConstraint_iff _ _ _ _).mp (by decide)))
  · intro i _; exact True.intro
  · intro i _ r hr; simp [quantifiedAbsenceDesc] at hr
  · exact List.nodup_nil
  · rw [satTrace_memLog]; simp
  · rw [satTrace_memLog]; exact True.intro
  · rw [satTrace_memLog]
    simp [Dregg2.Crypto.MemoryChecking.MemCheck, Dregg2.Crypto.MemoryChecking.initSet,
      Dregg2.Crypto.MemoryChecking.finalSet]
  · rw [satTrace_memLog]; rfl
  · rw [satTrace_mapLog]; rfl

/-- **`quantifiedAbsence_sat_relation` — the honest witness, carried THROUGH the bridge.** Composing the
satisfying trace with `quantifiedAbsence_refines` yields a concrete instance of the genuine relation on
`satTrace`'s row-0 columns (which are exactly the witness `elem=1, w=3, v=5, Acc_all=8, α=2` in limb 0). -/
theorem quantifiedAbsence_sat_relation (hash : List ℤ → ℤ) :
    QuotientAbsenceRel
      ((envAt satTrace 0).loc E0, (envAt satTrace 0).loc E1,
       (envAt satTrace 0).loc E2, (envAt satTrace 0).loc E3)
      ((envAt satTrace 0).loc Q0, (envAt satTrace 0).loc Q1,
       (envAt satTrace 0).loc Q2, (envAt satTrace 0).loc Q3)
      ((envAt satTrace 0).loc V0, (envAt satTrace 0).loc V1,
       (envAt satTrace 0).loc V2, (envAt satTrace 0).loc V3)
      ((envAt satTrace 0).pub (PI_ACC0 + 0), (envAt satTrace 0).pub (PI_ACC0 + 1),
       (envAt satTrace 0).pub (PI_ACC0 + 2), (envAt satTrace 0).pub (PI_ACC0 + 3))
      ((envAt satTrace 0).pub (PI_ALPHA0 + 0), (envAt satTrace 0).pub (PI_ALPHA0 + 1),
       (envAt satTrace 0).pub (PI_ALPHA0 + 2), (envAt satTrace 0).pub (PI_ALPHA0 + 3)) :=
  quantifiedAbsence_refines (quantifiedAbsence_sat hash) (by decide)

/-- The authored relation genuinely DISCRIMINATES (the anti-vacuity bits): true on the honest
`Acc_all = 8`, false when `Acc_all` is perturbed to `9`. -/
theorem quotientAbsenceRel_true :
    QuotientAbsenceRel (1, 0, 0, 0) (3, 0, 0, 0) (5, 0, 0, 0) (8, 0, 0, 0) (2, 0, 0, 0) := by
  unfold QuotientAbsenceRel extAdd extMul extSub; refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem quotientAbsenceRel_false :
    ¬ QuotientAbsenceRel (1, 0, 0, 0) (3, 0, 0, 0) (5, 0, 0, 0) (9, 0, 0, 0) (2, 0, 0, 0) := by
  unfold QuotientAbsenceRel extAdd extMul extSub
  intro hrel; exact absurd hrel.1 (by decide)

/-! ### The FAILING witness — the same trace with `sum[0]` perturbed to `999`, so the `sum = Acc_all`
pin (`loc S0 = pub[0]`) is violated: `999 ≠ 8`. -/

/-- Row 0 with the sum limb-0 column corrupted (`S0 = 999`, everything else as `satRow0`). -/
def badRow0 : Assignment := fun n =>
  [1,0,0,0, 3,0,0,0, 5,0,0,0, 1,0,0,0, 3,0,0,0, 999,0,0,0, 2,0,0,0].getD n 0

/-- The failing 2-row trace. -/
def badTrace : VmTrace := { rows := [badRow0, zeroAsg], pub := satPub, tf := fun _ => [] }

/-- **`quantifiedAbsence_bad` — a concrete assignment that FAILS `Satisfied2` (the constraint bites).**
The corrupted `sum[0] = 999` breaks the boundary PI pin `sum = Acc_all` (which demands `999 = 8`), so no
`hash`/boundary/table choice can make the descriptor accept it. -/
theorem quantifiedAbsence_bad (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) :
    ¬ Satisfied2 hash quantifiedAbsenceDesc minit mfin maddrs badTrace := by
  intro hsat
  have g := pin_holds0 hsat (by decide) S0 (PI_ACC0 + 0)
    (mem_of_sumPin (List.mem_cons.mpr (Or.inl rfl)))
  exact absurd g (by decide)

/-! ## §6 — Axiom-hygiene tripwires. -/

#assert_axioms quantifiedAbsence_refines
#assert_axioms quantifiedAbsence_sat
#assert_axioms quantifiedAbsence_sat_relation
#assert_axioms quantifiedAbsence_bad

end Dregg2.Circuit.Emit.QuantifiedAbsenceRefine

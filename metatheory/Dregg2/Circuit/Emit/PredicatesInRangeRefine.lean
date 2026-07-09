/-
# Dregg2.Circuit.Emit.PredicatesInRangeRefine — Rung-1 + Rung-2 for `predicateInRangeDesc`.

Two range teeth: `DIFF_LO = value − lo ∈ [0, 2^29)` (`value ≥ lo`) and `DIFF_HI = hi − value ∈ [0,
2^29)` (`value ≤ hi`). Rung-2 no-forgery: a `value < lo` run has `DIFF_LO < 0` — the low range tooth
is UNSAT.

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.PredicatesInRangeEmit

namespace Dregg2.Circuit.Emit.PredicatesInRangeRefine

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit
  (VmConstraint VmRowEnv VmRange holdsVm_gate_false holdsVm_piFirst_true)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.PredicatesInRangeEmit

set_option autoImplicit false
set_option maxRecDepth 8000

/-- **`ArithInRangeSem env`** — the `InRange(lo ≤ value ≤ hi)` relation: the private input value lies
in `[pub PI_LO, pub PI_HI]`, each gap bounded, and a bound fact commitment. -/
structure ArithInRangeSem (env : VmRowEnv) : Prop where
  lo_le     : env.pub PI_LO ≤ env.loc INPUT
  le_hi     : env.loc INPUT ≤ env.pub PI_HI
  domainLo  : env.loc INPUT - env.pub PI_LO < (2 : ℤ) ^ DIFF_BITS
  domainHi  : env.pub PI_HI - env.loc INPUT < (2 : ℤ) ^ DIFF_BITS
  factBinds : env.loc FACT_COMMITMENT = env.pub PI_FACT_COMMITMENT

theorem mem_c1lo : c1LoPin ∈ predicateInRangeDesc.constraints :=
  List.mem_cons.mpr (Or.inl rfl)
theorem mem_c1hi : c1HiPin ∈ predicateInRangeDesc.constraints :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
theorem mem_c2 : c2FactPin ∈ predicateInRangeDesc.constraints :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))
theorem mem_c3 : c3SlotGate ∈ predicateInRangeDesc.constraints :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr
    (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))
theorem mem_c5lo : c5LoGate ∈ predicateInRangeDesc.constraints := by
  simp only [predicateInRangeDesc]
  apply List.mem_cons_of_mem; apply List.mem_cons_of_mem; apply List.mem_cons_of_mem
  apply List.mem_cons_of_mem; exact List.mem_cons_self
theorem mem_c5hi : c5HiGate ∈ predicateInRangeDesc.constraints := by
  simp only [predicateInRangeDesc]
  apply List.mem_cons_of_mem; apply List.mem_cons_of_mem; apply List.mem_cons_of_mem
  apply List.mem_cons_of_mem; apply List.mem_cons_of_mem; exact List.mem_cons_self
theorem mem_c6lo : c6LoRange ∈ predicateInRangeDesc.constraints := by
  simp only [predicateInRangeDesc]
  apply List.mem_cons_of_mem; apply List.mem_cons_of_mem; apply List.mem_cons_of_mem
  apply List.mem_cons_of_mem; apply List.mem_cons_of_mem; apply List.mem_cons_of_mem
  exact List.mem_cons_self
theorem mem_c6hi : c6HiRange ∈ predicateInRangeDesc.constraints := by
  simp only [predicateInRangeDesc]
  apply List.mem_cons_of_mem; apply List.mem_cons_of_mem; apply List.mem_cons_of_mem
  apply List.mem_cons_of_mem; apply List.mem_cons_of_mem; apply List.mem_cons_of_mem
  apply List.mem_cons_of_mem; exact List.mem_cons_self

theorem memOpsOf_pred : memOpsOf predicateInRangeDesc = [] := rfl
theorem mapOpsOf_pred : mapOpsOf predicateInRangeDesc = [] := rfl
theorem memLog_pred (t : VmTrace) : memLog predicateInRangeDesc t = [] := by
  simp [memLog, memOpsOf_pred]
theorem mapLog_pred (t : VmTrace) : mapLog predicateInRangeDesc t = [] := by
  simp [mapLog, mapOpsOf_pred]

/-- **`predicateInRange_sat_imp_sem` (RUNG-1).** -/
theorem predicateInRange_sat_imp_sem {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hrange : t.tf .range = rangeRows DIFF_BITS)
    (hlen : 2 ≤ t.rows.length)
    (hsat : Satisfied2 hash predicateInRangeDesc minit mfin maddrs t) :
    ArithInRangeSem (envAt t 0) := by
  have h0 : 0 < t.rows.length := by omega
  have hfirst : ((0 : Nat) == 0) = true := rfl
  have hlast : ((0 : Nat) + 1 == t.rows.length) = false := by
    have : (0 : Nat) + 1 ≠ t.rows.length := by omega
    simpa using this
  have hc1lo : (envAt t 0).loc LO = (envAt t 0).pub PI_LO := by
    have h := hsat.rowConstraints 0 h0 c1LoPin mem_c1lo
    rw [hfirst] at h
    simpa only [c1LoPin, VmConstraint2.holdsAt, holdsVm_piFirst_true] using h
  have hc1hi : (envAt t 0).loc HI = (envAt t 0).pub PI_HI := by
    have h := hsat.rowConstraints 0 h0 c1HiPin mem_c1hi
    rw [hfirst] at h
    simpa only [c1HiPin, VmConstraint2.holdsAt, holdsVm_piFirst_true] using h
  have hc2 : (envAt t 0).loc FACT_COMMITMENT = (envAt t 0).pub PI_FACT_COMMITMENT := by
    have h := hsat.rowConstraints 0 h0 c2FactPin mem_c2
    rw [hfirst] at h
    simpa only [c2FactPin, VmConstraint2.holdsAt, holdsVm_piFirst_true] using h
  have hc3 : (envAt t 0).loc SLOT_A = (envAt t 0).loc INPUT := by
    have h := hsat.rowConstraints 0 h0 c3SlotGate mem_c3
    rw [hlast] at h
    simp only [c3SlotGate, VmConstraint2.holdsAt, holdsVm_gate_false] at h
    exact (c3_body_zero_iff (envAt t 0).loc).mp h
  have hc5lo : (envAt t 0).loc DIFF_LO = (envAt t 0).loc SLOT_A - (envAt t 0).loc LO := by
    have h := hsat.rowConstraints 0 h0 c5LoGate mem_c5lo
    rw [hlast] at h
    simp only [c5LoGate, VmConstraint2.holdsAt, holdsVm_gate_false] at h
    exact (c5Lo_body_zero_iff (envAt t 0).loc).mp h
  have hc5hi : (envAt t 0).loc DIFF_HI = (envAt t 0).loc HI - (envAt t 0).loc SLOT_A := by
    have h := hsat.rowConstraints 0 h0 c5HiGate mem_c5hi
    rw [hlast] at h
    simp only [c5HiGate, VmConstraint2.holdsAt, holdsVm_gate_false] at h
    exact (c5Hi_body_zero_iff (envAt t 0).loc).mp h
  have hc6lo : 0 ≤ (envAt t 0).loc DIFF_LO ∧ (envAt t 0).loc DIFF_LO < (2 : ℤ) ^ DIFF_BITS := by
    have h := hsat.rowConstraints 0 h0 c6LoRange mem_c6lo
    simp only [c6LoRange, VmConstraint2.holdsAt] at h
    have hv := lookup_replaces_range DIFF_BITS t.tf hrange (envAt t 0) DIFF_LO h
    simpa only [VmRange.holds] using hv
  have hc6hi : 0 ≤ (envAt t 0).loc DIFF_HI ∧ (envAt t 0).loc DIFF_HI < (2 : ℤ) ^ DIFF_BITS := by
    have h := hsat.rowConstraints 0 h0 c6HiRange mem_c6hi
    simp only [c6HiRange, VmConstraint2.holdsAt] at h
    have hv := lookup_replaces_range DIFF_BITS t.tf hrange (envAt t 0) DIFF_HI h
    simpa only [VmRange.holds] using hv
  obtain ⟨hlolo, hlohi⟩ := hc6lo
  obtain ⟨hhilo, hhihi⟩ := hc6hi
  exact ⟨by omega, by omega, by omega, by omega, hc2⟩

def rowOf (cols : List ℤ) : Assignment := fun i => cols.getD i 0
def hash0 : List ℤ → ℤ := fun _ => 0

/-- The honest satisfying assignment: `10 ≤ value = 40 ≤ 100`; `diff_lo = 30`, `diff_hi = 60`. -/
def inAsg : Assignment := rowOf [40, 40, 10, 100, 30, 60, 0]
def inPub : Assignment := rowOf [10, 100, 0]
def inTf : TraceFamily
  | TableId.range => rangeRows DIFF_BITS
  | _ => []
def inWitnessTrace : VmTrace := { rows := [inAsg, inAsg], pub := inPub, tf := inTf }

theorem inWitnessTf_range : inWitnessTrace.tf .range = rangeRows DIFF_BITS := by
  simp only [inWitnessTrace, inTf]

theorem inWitness_satisfies :
    Satisfied2 hash0 predicateInRangeDesc (fun _ => 0) (fun _ => (0, 0)) [] inWitnessTrace where
  rowConstraints := by
    intro i hi c hc
    have h30 : ([(30 : ℤ)] : List ℤ) ∈ rangeRows DIFF_BITS :=
      (range_row_mem_iff 30 DIFF_BITS).mpr (by norm_num [DIFF_BITS])
    have h60 : ([(60 : ℤ)] : List ℤ) ∈ rangeRows DIFF_BITS :=
      (range_row_mem_iff 60 DIFF_BITS).mpr (by norm_num [DIFF_BITS])
    have g0 : ((0 : Nat) + 1 == inWitnessTrace.rows.length) = false := rfl
    have g1 : ((1 : Nat) + 1 == inWitnessTrace.rows.length) = true := rfl
    have hlo0 : (envAt inWitnessTrace 0).loc DIFF_LO = 30 := by decide
    have hlo1 : (envAt inWitnessTrace 1).loc DIFF_LO = 30 := by decide
    have hhi0 : (envAt inWitnessTrace 0).loc DIFF_HI = 60 := by decide
    have hhi1 : (envAt inWitnessTrace 1).loc DIFF_HI = 60 := by decide
    have gllo0 : Lookup.holdsAt inWitnessTrace.tf (envAt inWitnessTrace 0)
        ⟨TableId.range, [.var DIFF_LO]⟩ := by
      simp only [Lookup.holdsAt, List.map_cons, List.map_nil, EmittedExpr.eval, inWitnessTf_range, hlo0]
      exact h30
    have gllo1 : Lookup.holdsAt inWitnessTrace.tf (envAt inWitnessTrace 1)
        ⟨TableId.range, [.var DIFF_LO]⟩ := by
      simp only [Lookup.holdsAt, List.map_cons, List.map_nil, EmittedExpr.eval, inWitnessTf_range, hlo1]
      exact h30
    have glhi0 : Lookup.holdsAt inWitnessTrace.tf (envAt inWitnessTrace 0)
        ⟨TableId.range, [.var DIFF_HI]⟩ := by
      simp only [Lookup.holdsAt, List.map_cons, List.map_nil, EmittedExpr.eval, inWitnessTf_range, hhi0]
      exact h60
    have glhi1 : Lookup.holdsAt inWitnessTrace.tf (envAt inWitnessTrace 1)
        ⟨TableId.range, [.var DIFF_HI]⟩ := by
      simp only [Lookup.holdsAt, List.map_cons, List.map_nil, EmittedExpr.eval, inWitnessTf_range, hhi1]
      exact h60
    have hi2 : i < 2 := hi
    clear hi
    simp only [predicateInRangeDesc] at hc
    interval_cases i <;>
      fin_cases hc <;>
      simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm,
        c1LoPin, c1HiPin, c2FactPin, c3SlotGate, c5LoGate, c5HiGate, c6LoRange, c6HiRange, g0, g1] <;>
      first
        | exact gllo0
        | exact gllo1
        | exact glhi0
        | exact glhi1
        | decide
  rowHashes := by intro i _; trivial
  rowRanges := by intro i _ r hr; simp only [predicateInRangeDesc, List.not_mem_nil] at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by intro op hop; rw [memLog_pred] at hop; simp at hop
  memDisciplined := by rw [memLog_pred]; trivial
  memBalanced := by rw [memLog_pred]; exact memCheck_nil _ _
  memTableFaithful := by rw [memLog_pred]; rfl
  mapTableFaithful := by rw [mapLog_pred]; rfl

theorem inWitness_sem : ArithInRangeSem (envAt inWitnessTrace 0) :=
  predicateInRange_sat_imp_sem (t := inWitnessTrace) inWitnessTf_range (by decide) inWitness_satisfies

theorem inWitness_sem_concrete :
    (envAt inWitnessTrace 0).pub PI_LO = 10
      ∧ (envAt inWitnessTrace 0).pub PI_HI = 100
      ∧ (envAt inWitnessTrace 0).loc INPUT = 40
      ∧ (envAt inWitnessTrace 0).pub PI_LO ≤ (envAt inWitnessTrace 0).loc INPUT
      ∧ (envAt inWitnessTrace 0).loc INPUT ≤ (envAt inWitnessTrace 0).pub PI_HI := by
  refine ⟨by decide, by decide, by decide, inWitness_sem.lo_le, inWitness_sem.le_hi⟩

/-- The HONEST below-range attempt: `value = 5 < lo = 10` (in `[lo, hi] = [10, 100]`). The honest
`diff_lo = value − lo = −5 < 0`; C3/C5lo/C5hi hold, only the C6lo range tooth rejects it. -/
def inBadAsg : Assignment := rowOf [5, 5, 10, 100, -5, 95, 0]
def inBadTrace : VmTrace := { rows := [inBadAsg, inBadAsg], pub := inPub, tf := inTf }

theorem inBadTf_range : inBadTrace.tf .range = rangeRows DIFF_BITS := by
  simp only [inBadTrace, inTf]

/-- **RUNG-2 (no-forgery): a below-range `value < lo` run PROVABLY FAILS `Satisfied2`.** -/
theorem inBad_not_satisfies :
    ¬ Satisfied2 hash0 predicateInRangeDesc (fun _ => 0) (fun _ => (0, 0)) [] inBadTrace := by
  intro h
  have h0 : (0 : Nat) < inBadTrace.rows.length := by decide
  have hrc := h.rowConstraints 0 h0 c6LoRange mem_c6lo
  simp only [c6LoRange, VmConstraint2.holdsAt] at hrc
  have hv := lookup_replaces_range DIFF_BITS inBadTrace.tf inBadTf_range (envAt inBadTrace 0) DIFF_LO hrc
  simp only [VmRange.holds] at hv
  have hx : (envAt inBadTrace 0).loc DIFF_LO = -5 := by decide
  rw [hx] at hv
  exact absurd hv.1 (by decide)

#assert_axioms predicateInRange_sat_imp_sem
#assert_axioms inWitness_satisfies
#assert_axioms inWitness_sem
#assert_axioms inWitness_sem_concrete
#assert_axioms inBad_not_satisfies

end Dregg2.Circuit.Emit.PredicatesInRangeRefine

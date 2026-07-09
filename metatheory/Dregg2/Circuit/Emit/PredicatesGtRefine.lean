/-
# Dregg2.Circuit.Emit.PredicatesGtRefine — Rung-1 + Rung-2 for `predicateGtDesc` (`>`).
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.PredicatesGtEmit

namespace Dregg2.Circuit.Emit.PredicatesGtRefine

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit
  (VmConstraint VmRowEnv VmRange holdsVm_gate_false holdsVm_piFirst_true)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.PredicatesGtEmit

set_option autoImplicit false
set_option maxRecDepth 8000

/-- **`ArithGtSem env`** — the `GreaterThan(value, threshold)` relation: the private input value is
STRICTLY `>` the public threshold, with a bounded gap, and a bound fact commitment. -/
structure ArithGtSem (env : VmRowEnv) : Prop where
  gt        : env.pub PI_THRESHOLD < env.loc INPUT
  domain    : env.loc INPUT - env.pub PI_THRESHOLD - 1 < (2 : ℤ) ^ DIFF_BITS
  factBinds : env.loc FACT_COMMITMENT = env.pub PI_FACT_COMMITMENT

theorem mem_c1 : c1ThresholdPin ∈ predicateGtDesc.constraints :=
  List.mem_cons.mpr (Or.inl rfl)
theorem mem_c2 : c2FactPin ∈ predicateGtDesc.constraints :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
theorem mem_c3 : c3SlotGate ∈ predicateGtDesc.constraints :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))
theorem mem_c5 : c5DiffGate ∈ predicateGtDesc.constraints :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr
    (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))
theorem mem_c6 : c6RangeLookup ∈ predicateGtDesc.constraints :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr
    (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

theorem memOpsOf_pred : memOpsOf predicateGtDesc = [] := rfl
theorem mapOpsOf_pred : mapOpsOf predicateGtDesc = [] := rfl
theorem memLog_pred (t : VmTrace) : memLog predicateGtDesc t = [] := by
  simp [memLog, memOpsOf_pred]
theorem mapLog_pred (t : VmTrace) : mapLog predicateGtDesc t = [] := by
  simp [mapLog, mapOpsOf_pred]

/-- **`predicateGt_sat_imp_sem` (RUNG-1).** -/
theorem predicateGt_sat_imp_sem {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hrange : t.tf .range = rangeRows DIFF_BITS)
    (hlen : 2 ≤ t.rows.length)
    (hsat : Satisfied2 hash predicateGtDesc minit mfin maddrs t) :
    ArithGtSem (envAt t 0) := by
  have h0 : 0 < t.rows.length := by omega
  have hfirst : ((0 : Nat) == 0) = true := rfl
  have hlast : ((0 : Nat) + 1 == t.rows.length) = false := by
    have : (0 : Nat) + 1 ≠ t.rows.length := by omega
    simpa using this
  have hc1 : (envAt t 0).loc THRESHOLD = (envAt t 0).pub PI_THRESHOLD := by
    have h := hsat.rowConstraints 0 h0 c1ThresholdPin mem_c1
    rw [hfirst] at h
    simpa only [c1ThresholdPin, VmConstraint2.holdsAt, holdsVm_piFirst_true] using h
  have hc2 : (envAt t 0).loc FACT_COMMITMENT = (envAt t 0).pub PI_FACT_COMMITMENT := by
    have h := hsat.rowConstraints 0 h0 c2FactPin mem_c2
    rw [hfirst] at h
    simpa only [c2FactPin, VmConstraint2.holdsAt, holdsVm_piFirst_true] using h
  have hc3 : (envAt t 0).loc SLOT_A = (envAt t 0).loc INPUT := by
    have h := hsat.rowConstraints 0 h0 c3SlotGate mem_c3
    rw [hlast] at h
    simp only [c3SlotGate, VmConstraint2.holdsAt, holdsVm_gate_false] at h
    exact (c3_body_zero_iff (envAt t 0).loc).mp h
  have hc5 : (envAt t 0).loc DIFF = (envAt t 0).loc SLOT_A - (envAt t 0).loc THRESHOLD - 1 := by
    have h := hsat.rowConstraints 0 h0 c5DiffGate mem_c5
    rw [hlast] at h
    simp only [c5DiffGate, VmConstraint2.holdsAt, holdsVm_gate_false] at h
    exact (c5_body_zero_iff (envAt t 0).loc).mp h
  have hc6 : 0 ≤ (envAt t 0).loc DIFF ∧ (envAt t 0).loc DIFF < (2 : ℤ) ^ DIFF_BITS := by
    have h := hsat.rowConstraints 0 h0 c6RangeLookup mem_c6
    simp only [c6RangeLookup, VmConstraint2.holdsAt] at h
    have hv := lookup_replaces_range DIFF_BITS t.tf hrange (envAt t 0) DIFF h
    simpa only [VmRange.holds] using hv
  obtain ⟨hlo, hhi⟩ := hc6
  exact ⟨by omega, by omega, hc2⟩

def rowOf (cols : List ℤ) : Assignment := fun i => cols.getD i 0
def hash0 : List ℤ → ℤ := fun _ => 0

/-- The honest satisfying assignment: `value = 101 > threshold = 40`, `diff = 101−40−1 = 60`. -/
def gtAsg : Assignment := rowOf [101, 101, 40, 60, 0]
def gtPub : Assignment := rowOf [40, 0]
def gtTf : TraceFamily
  | TableId.range => rangeRows DIFF_BITS
  | _ => []
def gtWitnessTrace : VmTrace := { rows := [gtAsg, gtAsg], pub := gtPub, tf := gtTf }

theorem gtWitnessTf_range : gtWitnessTrace.tf .range = rangeRows DIFF_BITS := by
  simp only [gtWitnessTrace, gtTf]

theorem gtWitness_satisfies :
    Satisfied2 hash0 predicateGtDesc (fun _ => 0) (fun _ => (0, 0)) [] gtWitnessTrace where
  rowConstraints := by
    intro i hi c hc
    have h60 : ([(60 : ℤ)] : List ℤ) ∈ rangeRows DIFF_BITS :=
      (range_row_mem_iff 60 DIFF_BITS).mpr (by norm_num [DIFF_BITS])
    have g0 : ((0 : Nat) + 1 == gtWitnessTrace.rows.length) = false := rfl
    have g1 : ((1 : Nat) + 1 == gtWitnessTrace.rows.length) = true := rfl
    have hd0 : (envAt gtWitnessTrace 0).loc DIFF = 60 := by decide
    have hd1 : (envAt gtWitnessTrace 1).loc DIFF = 60 := by decide
    have gl0 : Lookup.holdsAt gtWitnessTrace.tf (envAt gtWitnessTrace 0)
        ⟨TableId.range, [.var DIFF]⟩ := by
      simp only [Lookup.holdsAt, List.map_cons, List.map_nil, EmittedExpr.eval, gtWitnessTf_range, hd0]
      exact h60
    have gl1 : Lookup.holdsAt gtWitnessTrace.tf (envAt gtWitnessTrace 1)
        ⟨TableId.range, [.var DIFF]⟩ := by
      simp only [Lookup.holdsAt, List.map_cons, List.map_nil, EmittedExpr.eval, gtWitnessTf_range, hd1]
      exact h60
    have hi2 : i < 2 := hi
    clear hi
    simp only [predicateGtDesc] at hc
    interval_cases i <;>
      fin_cases hc <;>
      simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm,
        c1ThresholdPin, c2FactPin, c3SlotGate, c5DiffGate, c6RangeLookup, g0, g1] <;>
      first
        | exact gl0
        | exact gl1
        | decide
  rowHashes := by intro i _; trivial
  rowRanges := by intro i _ r hr; simp only [predicateGtDesc, List.not_mem_nil] at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by intro op hop; rw [memLog_pred] at hop; simp at hop
  memDisciplined := by rw [memLog_pred]; trivial
  memBalanced := by rw [memLog_pred]; exact memCheck_nil _ _
  memTableFaithful := by rw [memLog_pred]; rfl
  mapTableFaithful := by rw [mapLog_pred]; rfl

theorem gtWitness_sem : ArithGtSem (envAt gtWitnessTrace 0) :=
  predicateGt_sat_imp_sem (t := gtWitnessTrace) gtWitnessTf_range (by decide) gtWitness_satisfies

theorem gtWitness_sem_concrete :
    (envAt gtWitnessTrace 0).pub PI_THRESHOLD = 40
      ∧ (envAt gtWitnessTrace 0).loc INPUT = 101
      ∧ (envAt gtWitnessTrace 0).pub PI_THRESHOLD < (envAt gtWitnessTrace 0).loc INPUT := by
  refine ⟨by decide, by decide, gtWitness_sem.gt⟩

/-- The HONEST non-strict attempt: `value = 40 = threshold = 40` (NOT `>`), `diff = 40−40−1 = −1`.
C3/C5 hold; only the C6 range tooth rejects it. -/
def gtBadAsg : Assignment := rowOf [40, 40, 40, -1, 0]
def gtBadTrace : VmTrace := { rows := [gtBadAsg, gtBadAsg], pub := gtPub, tf := gtTf }

theorem gtBadTf_range : gtBadTrace.tf .range = rangeRows DIFF_BITS := by
  simp only [gtBadTrace, gtTf]

/-- **RUNG-2 (no-forgery): a non-strict `value = threshold` run PROVABLY FAILS `Satisfied2`.** -/
theorem gtBad_not_satisfies :
    ¬ Satisfied2 hash0 predicateGtDesc (fun _ => 0) (fun _ => (0, 0)) [] gtBadTrace := by
  intro h
  have h0 : (0 : Nat) < gtBadTrace.rows.length := by decide
  have hrc := h.rowConstraints 0 h0 c6RangeLookup mem_c6
  simp only [c6RangeLookup, VmConstraint2.holdsAt] at hrc
  have hv := lookup_replaces_range DIFF_BITS gtBadTrace.tf gtBadTf_range (envAt gtBadTrace 0) DIFF hrc
  simp only [VmRange.holds] at hv
  have hx : (envAt gtBadTrace 0).loc DIFF = -1 := by decide
  rw [hx] at hv
  exact absurd hv.1 (by decide)

#assert_axioms predicateGt_sat_imp_sem
#assert_axioms gtWitness_satisfies
#assert_axioms gtWitness_sem
#assert_axioms gtWitness_sem_concrete
#assert_axioms gtBad_not_satisfies

end Dregg2.Circuit.Emit.PredicatesGtRefine

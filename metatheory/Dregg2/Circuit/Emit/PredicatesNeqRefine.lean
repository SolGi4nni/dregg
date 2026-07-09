/-
# Dregg2.Circuit.Emit.PredicatesNeqRefine — Rung-1 + Rung-2 for `predicateNeqDesc` (`≠`).

The `≠` case has no range tooth: soundness rides the nonzero-inverse gadget CNZ
(`DIFF · DIFF_INV = 1 ⟹ DIFF ≠ 0 ⟹ value ≠ threshold`). Rung-2 no-forgery: a `value = threshold`
run forces `DIFF = 0`, and `0 · DIFF_INV = 0 ≠ 1` — the CNZ tooth is UNSAT.

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.PredicatesNeqEmit

namespace Dregg2.Circuit.Emit.PredicatesNeqRefine

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit
  (VmConstraint VmRowEnv holdsVm_gate_false holdsVm_piFirst_true)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.PredicatesNeqEmit

set_option autoImplicit false
set_option maxRecDepth 8000

/-- **`ArithNeqSem env`** — the `NotEqual(value, threshold)` relation: the private input value is
`≠` the public threshold, and the published fact commitment binds its public input. -/
structure ArithNeqSem (env : VmRowEnv) : Prop where
  neq       : env.loc INPUT ≠ env.pub PI_THRESHOLD
  factBinds : env.loc FACT_COMMITMENT = env.pub PI_FACT_COMMITMENT

theorem mem_c1 : c1ThresholdPin ∈ predicateNeqDesc.constraints :=
  List.mem_cons.mpr (Or.inl rfl)
theorem mem_c2 : c2FactPin ∈ predicateNeqDesc.constraints :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
theorem mem_c3 : c3SlotGate ∈ predicateNeqDesc.constraints :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))
theorem mem_c5 : c5DiffGate ∈ predicateNeqDesc.constraints :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr
    (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))
theorem mem_cNz : cNzGate ∈ predicateNeqDesc.constraints :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr
    (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

theorem memOpsOf_pred : memOpsOf predicateNeqDesc = [] := rfl
theorem mapOpsOf_pred : mapOpsOf predicateNeqDesc = [] := rfl
theorem memLog_pred (t : VmTrace) : memLog predicateNeqDesc t = [] := by
  simp [memLog, memOpsOf_pred]
theorem mapLog_pred (t : VmTrace) : mapLog predicateNeqDesc t = [] := by
  simp [mapLog, mapOpsOf_pred]

/-- **`predicateNeq_sat_imp_sem` (RUNG-1).** A satisfying trace computes the genuine `≠` relation on
row 0 — the nonzero-inverse tooth forces `DIFF = value − threshold ≠ 0`. -/
theorem predicateNeq_sat_imp_sem {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hlen : 2 ≤ t.rows.length)
    (hsat : Satisfied2 hash predicateNeqDesc minit mfin maddrs t) :
    ArithNeqSem (envAt t 0) := by
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
  have hc5 : (envAt t 0).loc DIFF = (envAt t 0).loc SLOT_A - (envAt t 0).loc THRESHOLD := by
    have h := hsat.rowConstraints 0 h0 c5DiffGate mem_c5
    rw [hlast] at h
    simp only [c5DiffGate, VmConstraint2.holdsAt, holdsVm_gate_false] at h
    exact (c5_body_zero_iff (envAt t 0).loc).mp h
  have hcnz : (envAt t 0).loc DIFF ≠ 0 := by
    have h := hsat.rowConstraints 0 h0 cNzGate mem_cNz
    rw [hlast] at h
    simp only [cNzGate, VmConstraint2.holdsAt, holdsVm_gate_false] at h
    exact cNz_body_zero_imp_ne (envAt t 0).loc h
  exact ⟨by omega, hc2⟩

def rowOf (cols : List ℤ) : Assignment := fun i => cols.getD i 0
def hash0 : List ℤ → ℤ := fun _ => 0

/-- The honest satisfying assignment: `value = 41 ≠ threshold = 40`, `diff = 1`, `diff_inv = 1`. -/
def neqAsg : Assignment := rowOf [41, 41, 40, 1, 1, 0]
def neqPub : Assignment := rowOf [40, 0]
def neqTf : TraceFamily := fun _ => []
def neqWitnessTrace : VmTrace := { rows := [neqAsg, neqAsg], pub := neqPub, tf := neqTf }

theorem neqWitness_satisfies :
    Satisfied2 hash0 predicateNeqDesc (fun _ => 0) (fun _ => (0, 0)) [] neqWitnessTrace where
  rowConstraints := by
    intro i hi c hc
    have g0 : ((0 : Nat) + 1 == neqWitnessTrace.rows.length) = false := rfl
    have g1 : ((1 : Nat) + 1 == neqWitnessTrace.rows.length) = true := rfl
    have hi2 : i < 2 := hi
    clear hi
    simp only [predicateNeqDesc] at hc
    interval_cases i <;>
      fin_cases hc <;>
      simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm,
        c1ThresholdPin, c2FactPin, c3SlotGate, c5DiffGate, cNzGate, g0, g1] <;>
      decide
  rowHashes := by intro i _; trivial
  rowRanges := by intro i _ r hr; simp only [predicateNeqDesc, List.not_mem_nil] at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by intro op hop; rw [memLog_pred] at hop; simp at hop
  memDisciplined := by rw [memLog_pred]; trivial
  memBalanced := by rw [memLog_pred]; exact memCheck_nil _ _
  memTableFaithful := by rw [memLog_pred]; rfl
  mapTableFaithful := by rw [mapLog_pred]; rfl

theorem neqWitness_sem : ArithNeqSem (envAt neqWitnessTrace 0) :=
  predicateNeq_sat_imp_sem (t := neqWitnessTrace) (by decide) neqWitness_satisfies

theorem neqWitness_sem_concrete :
    (envAt neqWitnessTrace 0).pub PI_THRESHOLD = 40
      ∧ (envAt neqWitnessTrace 0).loc INPUT = 41
      ∧ (envAt neqWitnessTrace 0).loc INPUT ≠ (envAt neqWitnessTrace 0).pub PI_THRESHOLD := by
  refine ⟨by decide, by decide, neqWitness_sem.neq⟩

/-- The HONEST equal-value attempt: `value = 40 = threshold = 40` (NOT `≠`). The honest diff is `0`
and no inverse exists (`diff_inv = 0`), so C1/C2/C3/C5 hold but the CNZ tooth `0·0 = 0 ≠ 1` fails. -/
def neqBadAsg : Assignment := rowOf [40, 40, 40, 0, 0, 0]
def neqBadTrace : VmTrace := { rows := [neqBadAsg, neqBadAsg], pub := neqPub, tf := neqTf }

/-- **RUNG-2 (no-forgery): an equal-value `value = threshold` run PROVABLY FAILS `Satisfied2`.**
The CNZ nonzero-inverse tooth cannot be satisfied when `DIFF = 0`. -/
theorem neqBad_not_satisfies :
    ¬ Satisfied2 hash0 predicateNeqDesc (fun _ => 0) (fun _ => (0, 0)) [] neqBadTrace := by
  intro h
  have h0 : (0 : Nat) < neqBadTrace.rows.length := by decide
  have hlast : ((0 : Nat) + 1 == neqBadTrace.rows.length) = false := rfl
  have hrc := h.rowConstraints 0 h0 cNzGate mem_cNz
  rw [hlast] at hrc
  simp only [cNzGate, VmConstraint2.holdsAt, holdsVm_gate_false] at hrc
  have hx : cNzBody.eval (envAt neqBadTrace 0).loc = -1 := by decide
  rw [hx] at hrc
  exact absurd hrc (by decide)

#assert_axioms predicateNeq_sat_imp_sem
#assert_axioms neqWitness_satisfies
#assert_axioms neqWitness_sem
#assert_axioms neqWitness_sem_concrete
#assert_axioms neqBad_not_satisfies

end Dregg2.Circuit.Emit.PredicatesNeqRefine

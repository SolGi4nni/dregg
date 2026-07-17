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
theorem mem_factHash : factHashLookup ∈ predicateNeqDesc.constraints := by
  simp only [predicateNeqDesc]
  apply List.mem_cons_of_mem; apply List.mem_cons_of_mem; apply List.mem_cons_of_mem
  apply List.mem_cons_of_mem; apply List.mem_cons_of_mem; exact List.mem_cons_self
theorem mem_factCommit : factCommitLookup ∈ predicateNeqDesc.constraints := by
  simp only [predicateNeqDesc]
  apply List.mem_cons_of_mem; apply List.mem_cons_of_mem; apply List.mem_cons_of_mem
  apply List.mem_cons_of_mem; apply List.mem_cons_of_mem; apply List.mem_cons_of_mem
  exact List.mem_cons_self

theorem memOpsOf_pred : memOpsOf predicateNeqDesc = [] := rfl
theorem mapOpsOf_pred : mapOpsOf predicateNeqDesc = [] := rfl
theorem memLog_pred (t : VmTrace) : memLog predicateNeqDesc t = [] := by
  simp [memLog, memOpsOf_pred]
theorem mapLog_pred (t : VmTrace) : mapLog predicateNeqDesc t = [] := by
  simp [mapLog, mapOpsOf_pred]

/-! The mod-`p` denotation makes the `≠` half PURELY MODULAR — no range/canonicality is needed for
it: the nonzero-inverse tooth gives `DIFF · DIFF_INV ≡ 1 [ZMOD p]`, so `p ∤ DIFF`, and the diff/slot
gates give `DIFF ≡ INPUT − pub [ZMOD p]`, whence `INPUT = pub` would force `p ∣ DIFF` — contradiction,
so `INPUT ≠ pub` over ℤ. Only the `factBinds` ℤ-equality needs the deployed range-check on the two
commitment cells; that is `NeqCanon`, inhabited by `neqWitness_canon`. -/
def NeqCanon (t : VmTrace) : Prop :=
  (0 ≤ (envAt t 0).loc FACT_COMMITMENT ∧ (envAt t 0).loc FACT_COMMITMENT < 2013265921)
  ∧ (0 ≤ (envAt t 0).pub PI_FACT_COMMITMENT ∧ (envAt t 0).pub PI_FACT_COMMITMENT < 2013265921)

/-- **`predicateNeq_sat_imp_sem` (RUNG-1).** A satisfying trace computes the genuine `≠` relation on
row 0 — the nonzero-inverse tooth forces `DIFF = value − threshold ≢ 0 [ZMOD p]`. -/
theorem predicateNeq_sat_imp_sem {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hlen : 2 ≤ t.rows.length)
    (hcanon : NeqCanon t)
    (hsat : Satisfied2 hash predicateNeqDesc minit mfin maddrs t) :
    ArithNeqSem (envAt t 0) := by
  obtain ⟨⟨hcF0, hcF1⟩, ⟨hcPF0, hcPF1⟩⟩ := hcanon
  have h0 : 0 < t.rows.length := by omega
  have hfirst : ((0 : Nat) == 0) = true := rfl
  have hlast : ((0 : Nat) + 1 == t.rows.length) = false := by
    have : (0 : Nat) + 1 ≠ t.rows.length := by omega
    simpa using this
  -- factBinds: the PI pin (mod `p`) lifted to a genuine ℤ equality by canonicality of both cells.
  have hc2 : (envAt t 0).loc FACT_COMMITMENT = (envAt t 0).pub PI_FACT_COMMITMENT := by
    have h := hsat.rowConstraints 0 h0 c2FactPin mem_c2
    rw [hfirst] at h
    have hm : (envAt t 0).loc FACT_COMMITMENT ≡ (envAt t 0).pub PI_FACT_COMMITMENT
        [ZMOD 2013265921] := by
      simpa only [c2FactPin, VmConstraint2.holdsAt, holdsVm_piFirst_true] using h
    rw [Int.modEq_iff_dvd] at hm; obtain ⟨k, hk⟩ := hm; omega
  -- the threshold PI pin as a divisibility fact.
  have hc1 : (2013265921 : ℤ) ∣ ((envAt t 0).pub PI_THRESHOLD - (envAt t 0).loc THRESHOLD) := by
    have h := hsat.rowConstraints 0 h0 c1ThresholdPin mem_c1
    rw [hfirst] at h
    have hm : (envAt t 0).loc THRESHOLD ≡ (envAt t 0).pub PI_THRESHOLD [ZMOD 2013265921] := by
      simpa only [c1ThresholdPin, VmConstraint2.holdsAt, holdsVm_piFirst_true] using h
    exact (Int.modEq_iff_dvd).mp hm
  -- the slot gate as a divisibility fact.
  have hc3 : (2013265921 : ℤ) ∣ ((envAt t 0).loc SLOT_A - (envAt t 0).loc INPUT) := by
    have h := hsat.rowConstraints 0 h0 c3SlotGate mem_c3
    rw [hlast] at h
    simp only [c3SlotGate, VmConstraint2.holdsAt, holdsVm_gate_false, c3Body, EmittedExpr.eval] at h
    have hkey : (envAt t 0).loc SLOT_A + -1 * (envAt t 0).loc INPUT
        = (envAt t 0).loc SLOT_A - (envAt t 0).loc INPUT := by ring
    rw [hkey, Int.modEq_zero_iff_dvd] at h; exact h
  -- the diff gate as a divisibility fact.
  have hc5 : (2013265921 : ℤ) ∣ ((envAt t 0).loc DIFF - (envAt t 0).loc SLOT_A
      + (envAt t 0).loc THRESHOLD) := by
    have h := hsat.rowConstraints 0 h0 c5DiffGate mem_c5
    rw [hlast] at h
    simp only [c5DiffGate, VmConstraint2.holdsAt, holdsVm_gate_false, c5Body, EmittedExpr.eval] at h
    rw [Int.modEq_zero_iff_dvd] at h
    -- `h : p ∣ c5Body-linear`; the body is `DIFF − SLOT_A + THRESHOLD` up to `ring`.
    have hkey : (envAt t 0).loc DIFF + -1 * (envAt t 0).loc SLOT_A + (envAt t 0).loc THRESHOLD
        = (envAt t 0).loc DIFF - (envAt t 0).loc SLOT_A + (envAt t 0).loc THRESHOLD := by ring
    rw [hkey] at h; exact h
  -- the nonzero-inverse tooth: `DIFF · DIFF_INV ≡ 1 [ZMOD p]`, so `p ∤ DIFF`.
  have hcnz : ¬ ((2013265921 : ℤ) ∣ (envAt t 0).loc DIFF) := by
    have h := hsat.rowConstraints 0 h0 cNzGate mem_cNz
    rw [hlast] at h
    simp only [cNzGate, VmConstraint2.holdsAt, holdsVm_gate_false, cNzBody, EmittedExpr.eval] at h
    rw [Int.modEq_zero_iff_dvd] at h
    -- h : p ∣ (DIFF * DIFF_INV + -1)
    intro hdvd
    have hprod : (2013265921 : ℤ) ∣ (envAt t 0).loc DIFF * (envAt t 0).loc DIFF_INV :=
      Dvd.dvd.mul_right hdvd _
    have hone : (2013265921 : ℤ) ∣ (1 : ℤ) := by
      have := Int.dvd_sub hprod h; simpa using this
    exact absurd (Int.le_of_dvd (by norm_num) hone) (by norm_num)
  refine ⟨?_, hc2⟩
  intro heq
  exact hcnz (by omega)

def rowOf (cols : List ℤ) : Assignment := fun i => cols.getD i 0
def hash0 : List ℤ → ℤ := fun _ => 0

/-- The honest satisfying assignment: `value = 41 ≠ threshold = 40`, `diff = 1`, `diff_inv = 1`. -/
def neqAsg : Assignment := rowOf [41, 41, 40, 1, 1, 0]
def neqPub : Assignment := rowOf [40, 0]
/-- The `≠` descriptor declares NO range table; the trace family carries ONLY the Poseidon2 chip
table with the two genuine `chipRow`s the weld lookups absorb (arity-7 fact-hash over `INPUT = 41`,
arity-2 fact-commitment). -/
def neqTf : TraceFamily
  | TableId.poseidon2 =>
      [chipRow hash0 [0, 41, 0, 0, 0, FACT_MARK, 1] (List.replicate 7 0),
       chipRow hash0 [0, 0, 0, 0] (List.replicate 7 0)]
  | _ => []
def neqWitnessTrace : VmTrace := { rows := [neqAsg, neqAsg], pub := neqPub, tf := neqTf }

theorem neqWitness_satisfies :
    Satisfied2 hash0 predicateNeqDesc (fun _ => 0) (fun _ => (0, 0)) [] neqWitnessTrace where
  rowConstraints := by
    intro i hi c hc
    have g0 : ((0 : Nat) + 1 == neqWitnessTrace.rows.length) = false := rfl
    have g1 : ((1 : Nat) + 1 == neqWitnessTrace.rows.length) = true := rfl
    -- the two weld chip lookups land in the concrete Poseidon2 chip table (decidable membership).
    have gph0 : Lookup.holdsAt neqWitnessTrace.tf (envAt neqWitnessTrace 0)
        ⟨TableId.poseidon2, chipLookupTuple [.var PREDICATE_SYM, .var INPUT, .var TERM1, .var TERM2,
          .const 0, .const FACT_MARK, .const 1] FACT_HASH FACTHASH_LANES⟩ := by
      simp only [Lookup.holdsAt, neqWitnessTrace, neqTf]; decide
    have gph1 : Lookup.holdsAt neqWitnessTrace.tf (envAt neqWitnessTrace 1)
        ⟨TableId.poseidon2, chipLookupTuple [.var PREDICATE_SYM, .var INPUT, .var TERM1, .var TERM2,
          .const 0, .const FACT_MARK, .const 1] FACT_HASH FACTHASH_LANES⟩ := by
      simp only [Lookup.holdsAt, neqWitnessTrace, neqTf]; decide
    have gpc0 : Lookup.holdsAt neqWitnessTrace.tf (envAt neqWitnessTrace 0)
        ⟨TableId.poseidon2, chipLookupTuple [.var FACT_HASH, .var STATE_ROOT, .var BLINDING, .const 0]
          FACT_COMMITMENT FACTCOMMIT_LANES⟩ := by
      simp only [Lookup.holdsAt, neqWitnessTrace, neqTf]; decide
    have gpc1 : Lookup.holdsAt neqWitnessTrace.tf (envAt neqWitnessTrace 1)
        ⟨TableId.poseidon2, chipLookupTuple [.var FACT_HASH, .var STATE_ROOT, .var BLINDING, .const 0]
          FACT_COMMITMENT FACTCOMMIT_LANES⟩ := by
      simp only [Lookup.holdsAt, neqWitnessTrace, neqTf]; decide
    have hi2 : i < 2 := hi
    clear hi
    simp only [predicateNeqDesc] at hc
    interval_cases i <;>
      fin_cases hc <;>
      simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm,
        c1ThresholdPin, c2FactPin, c3SlotGate, c5DiffGate, cNzGate,
        factHashLookup, factCommitLookup, g0, g1] <;>
      first
        | exact gph0
        | exact gph1
        | exact gpc0
        | exact gpc1
        | decide
  rowHashes := by intro i _; trivial
  rowRanges := by intro i _ r hr; simp only [predicateNeqDesc, List.not_mem_nil] at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by intro op hop; rw [memLog_pred] at hop; simp at hop
  memDisciplined := by rw [memLog_pred]; trivial
  memBalanced := by rw [memLog_pred]; exact memCheck_nil _ _
  memTableFaithful := by rw [memLog_pred]; rfl
  mapTableFaithful := by rw [mapLog_pred]; rfl

theorem neqWitness_canon : NeqCanon neqWitnessTrace := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

theorem neqWitness_sem : ArithNeqSem (envAt neqWitnessTrace 0) :=
  predicateNeq_sat_imp_sem (t := neqWitnessTrace) (by decide) neqWitness_canon neqWitness_satisfies

theorem neqWitness_sem_concrete :
    (envAt neqWitnessTrace 0).pub PI_THRESHOLD = 40
      ∧ (envAt neqWitnessTrace 0).loc INPUT = 41
      ∧ (envAt neqWitnessTrace 0).loc INPUT ≠ (envAt neqWitnessTrace 0).pub PI_THRESHOLD := by
  refine ⟨by decide, by decide, neqWitness_sem.neq⟩

/-! ## §5b — THE VALUE↔FACT WELD: the committed fact carries the proven value. -/

/-- **`predicateNeq_fact_opens_to_input`** — the public fact commitment opens, in the genuine hash, to
the DOUBLE hash of a fact whose value slot is the SAME `INPUT` the `≠` gadget speaks about. -/
theorem predicateNeq_fact_opens_to_input {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (hlen : 2 ≤ t.rows.length)
    (hcanon : NeqCanon t)
    (hsat : Satisfied2 hash predicateNeqDesc minit mfin maddrs t) :
    (envAt t 0).pub PI_FACT_COMMITMENT
      = hash [hash [(envAt t 0).loc PREDICATE_SYM, (envAt t 0).loc INPUT,
                    (envAt t 0).loc TERM1, (envAt t 0).loc TERM2, 0, FACT_MARK, 1],
              (envAt t 0).loc STATE_ROOT, (envAt t 0).loc BLINDING, 0] := by
  obtain ⟨⟨hcF0, hcF1⟩, ⟨hcPF0, hcPF1⟩⟩ := hcanon
  have h0 : 0 < t.rows.length := by omega
  have hc2 : (envAt t 0).loc FACT_COMMITMENT = (envAt t 0).pub PI_FACT_COMMITMENT := by
    have h := hsat.rowConstraints 0 h0 c2FactPin mem_c2
    rw [show ((0 : Nat) == 0) = true from rfl] at h
    have hm : (envAt t 0).loc FACT_COMMITMENT ≡ (envAt t 0).pub PI_FACT_COMMITMENT
        [ZMOD 2013265921] := by
      simpa only [c2FactPin, VmConstraint2.holdsAt, holdsVm_piFirst_true] using h
    rw [Int.modEq_iff_dvd] at hm; obtain ⟨k, hk⟩ := hm; omega
  have hlF := hsat.rowConstraints 0 h0 factHashLookup mem_factHash
  simp only [VmConstraint2.holdsAt, factHashLookup, Lookup.holdsAt] at hlF
  have hfh := chip_lookup_sound hash (t.tf .poseidon2) hChip (envAt t 0).loc
    [.var PREDICATE_SYM, .var INPUT, .var TERM1, .var TERM2, .const 0, .const FACT_MARK, .const 1]
    FACT_HASH FACTHASH_LANES (by decide) hlF
  simp only [List.map_cons, List.map_nil, EmittedExpr.eval] at hfh
  have hlC := hsat.rowConstraints 0 h0 factCommitLookup mem_factCommit
  simp only [VmConstraint2.holdsAt, factCommitLookup, Lookup.holdsAt] at hlC
  have hfc := chip_lookup_sound hash (t.tf .poseidon2) hChip (envAt t 0).loc
    [.var FACT_HASH, .var STATE_ROOT, .var BLINDING, .const 0] FACT_COMMITMENT FACTCOMMIT_LANES
    (by decide) hlC
  simp only [List.map_cons, List.map_nil, EmittedExpr.eval] at hfc
  rw [← hc2, hfc, hfh]

/-- **THE WELD BITES (value ≠ committed value ⟹ REJECT).** -/
theorem predicateNeq_value_forge_rejected {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (hlen : 2 ≤ t.rows.length) (hcanon : NeqCanon t) (v0 : ℤ)
    (hcred : (envAt t 0).pub PI_FACT_COMMITMENT
      = hash [hash [(envAt t 0).loc PREDICATE_SYM, v0, (envAt t 0).loc TERM1,
                    (envAt t 0).loc TERM2, 0, FACT_MARK, 1], (envAt t 0).loc STATE_ROOT,
              (envAt t 0).loc BLINDING, 0])
    (hinj : ∀ a b : ℤ,
      hash [hash [(envAt t 0).loc PREDICATE_SYM, a, (envAt t 0).loc TERM1,
                  (envAt t 0).loc TERM2, 0, FACT_MARK, 1], (envAt t 0).loc STATE_ROOT,
            (envAt t 0).loc BLINDING, 0]
        = hash [hash [(envAt t 0).loc PREDICATE_SYM, b, (envAt t 0).loc TERM1,
                  (envAt t 0).loc TERM2, 0, FACT_MARK, 1], (envAt t 0).loc STATE_ROOT,
                (envAt t 0).loc BLINDING, 0] → a = b)
    (hforge : (envAt t 0).loc INPUT ≠ v0) :
    ¬ Satisfied2 hash predicateNeqDesc minit mfin maddrs t := by
  intro hsat
  have hopen := predicateNeq_fact_opens_to_input hChip hlen hcanon hsat
  exact hforge (hinj _ _ (hopen.symm.trans hcred))

/-- The concrete Poseidon2 chip table is genuinely SOUND for `hash0`. -/
theorem neqChipSound : ChipTableSound hash0 (neqWitnessTrace.tf .poseidon2) := by
  intro r hr
  simp only [neqWitnessTrace, neqTf, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h
  · exact ⟨[0, 41, 0, 0, 0, FACT_MARK, 1], List.replicate 7 0, by decide, by decide, h⟩
  · exact ⟨[0, 0, 0, 0], List.replicate 7 0, by decide, by decide, h⟩

/-- **The value↔fact WELD leg FIRES on the witness (non-vacuously).** -/
theorem neqWitness_fact_opens :
    (envAt neqWitnessTrace 0).pub PI_FACT_COMMITMENT
      = hash0 [hash0 [(envAt neqWitnessTrace 0).loc PREDICATE_SYM, (envAt neqWitnessTrace 0).loc INPUT,
                (envAt neqWitnessTrace 0).loc TERM1, (envAt neqWitnessTrace 0).loc TERM2,
                0, FACT_MARK, 1], (envAt neqWitnessTrace 0).loc STATE_ROOT,
                (envAt neqWitnessTrace 0).loc BLINDING, 0] :=
  predicateNeq_fact_opens_to_input (t := neqWitnessTrace) neqChipSound (by decide) neqWitness_canon
    neqWitness_satisfies

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
#assert_axioms predicateNeq_fact_opens_to_input
#assert_axioms predicateNeq_value_forge_rejected
#assert_axioms neqChipSound
#assert_axioms neqWitness_fact_opens
#assert_axioms neqWitness_satisfies
#assert_axioms neqWitness_sem
#assert_axioms neqWitness_sem_concrete
#assert_axioms neqBad_not_satisfies

end Dregg2.Circuit.Emit.PredicatesNeqRefine

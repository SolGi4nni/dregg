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
theorem mem_factHash : factHashLookup ∈ predicateGtDesc.constraints := by
  simp only [predicateGtDesc]
  apply List.mem_cons_of_mem; apply List.mem_cons_of_mem; apply List.mem_cons_of_mem
  apply List.mem_cons_of_mem; apply List.mem_cons_of_mem; exact List.mem_cons_self
theorem mem_factCommit : factCommitLookup ∈ predicateGtDesc.constraints := by
  simp only [predicateGtDesc]
  apply List.mem_cons_of_mem; apply List.mem_cons_of_mem; apply List.mem_cons_of_mem
  apply List.mem_cons_of_mem; apply List.mem_cons_of_mem; apply List.mem_cons_of_mem
  exact List.mem_cons_self

theorem memOpsOf_pred : memOpsOf predicateGtDesc = [] := rfl
theorem mapOpsOf_pred : mapOpsOf predicateGtDesc = [] := rfl
theorem memLog_pred (t : VmTrace) : memLog predicateGtDesc t = [] := by
  simp [memLog, memOpsOf_pred]
theorem mapLog_pred (t : VmTrace) : mapLog predicateGtDesc t = [] := by
  simp [mapLog, mapOpsOf_pred]

/-! ## §3b — the deployed range-check canonicality envelope.

Under the field-faithful mod-`p` denotation every PI pin / gate binds only a CONGRUENCE
(`≡ … [ZMOD 2013265921]`), not a genuine ℤ equality. The deployed range-check discipline is what
reads the ℤ semantics back off it: the `THRESHOLD` / `INPUT` / `SLOT_A` cells sit in the LOW HALF of
the field (`2·x < p`) — the wrap-free window that makes `DIFF = SLOT_A − THRESHOLD − 1` (with
`DIFF ∈ [0, 2^29) ⊂ [0, p/2)`, from the C6 range lookup) a genuine ℤ identity, not a mod-`p`
underflow — and the two commitment cells / both public inputs are canonical (`0 ≤ · < p`). Inhabited
concretely by `gtWitness_canon`, so the envelope is non-vacuous. -/
def GtCanon (t : VmTrace) : Prop :=
  (0 ≤ (envAt t 0).loc INPUT ∧ 2 * (envAt t 0).loc INPUT < 2013265921)
  ∧ (0 ≤ (envAt t 0).loc SLOT_A ∧ 2 * (envAt t 0).loc SLOT_A < 2013265921)
  ∧ (0 ≤ (envAt t 0).loc THRESHOLD ∧ 2 * (envAt t 0).loc THRESHOLD < 2013265921)
  ∧ (0 ≤ (envAt t 0).loc FACT_COMMITMENT ∧ (envAt t 0).loc FACT_COMMITMENT < 2013265921)
  ∧ (0 ≤ (envAt t 0).pub PI_THRESHOLD ∧ (envAt t 0).pub PI_THRESHOLD < 2013265921)
  ∧ (0 ≤ (envAt t 0).pub PI_FACT_COMMITMENT ∧ (envAt t 0).pub PI_FACT_COMMITMENT < 2013265921)

/-- **`predicateGt_sat_imp_sem` (RUNG-1).** Under the mod-`p` denotation each pin/gate binds a
congruence; the deployed range-check envelope (`GtCanon`) lifts them to the genuine ℤ relation. -/
theorem predicateGt_sat_imp_sem {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hrange : t.tf .range = rangeRows DIFF_BITS)
    (hlen : 2 ≤ t.rows.length)
    (hcanon : GtCanon t)
    (hsat : Satisfied2 hash predicateGtDesc minit mfin maddrs t) :
    ArithGtSem (envAt t 0) := by
  obtain ⟨⟨hcI0, hcI1⟩, ⟨hcS0, hcS1⟩, ⟨hcT0, hcT1⟩, ⟨hcF0, hcF1⟩, ⟨hcPT0, hcPT1⟩, ⟨hcPF0, hcPF1⟩⟩ :=
    hcanon
  have h0 : 0 < t.rows.length := by omega
  have hfirst : ((0 : Nat) == 0) = true := rfl
  have hlast : ((0 : Nat) + 1 == t.rows.length) = false := by
    have : (0 : Nat) + 1 ≠ t.rows.length := by omega
    simpa using this
  -- C6 range lookup: `DIFF ∈ [0, 2^29)` — a GENUINE ℤ bound (the lookup denotation is not mod-`p`).
  have hc6 : 0 ≤ (envAt t 0).loc DIFF ∧ (envAt t 0).loc DIFF < (2 : ℤ) ^ DIFF_BITS := by
    have h := hsat.rowConstraints 0 h0 c6RangeLookup mem_c6
    simp only [c6RangeLookup, VmConstraint2.holdsAt] at h
    have hv := lookup_replaces_range DIFF_BITS t.tf hrange (envAt t 0) DIFF h
    simpa only [VmRange.holds] using hv
  obtain ⟨hlo, hhi⟩ := hc6
  have hpow : (2 : ℤ) ^ DIFF_BITS = 536870912 := by norm_num [DIFF_BITS]
  rw [hpow] at hhi
  -- C1 threshold PI pin (mod `p`), lifted to ℤ by canonicality of both cells.
  have hc1 : (envAt t 0).loc THRESHOLD = (envAt t 0).pub PI_THRESHOLD := by
    have h := hsat.rowConstraints 0 h0 c1ThresholdPin mem_c1
    rw [hfirst] at h
    have hm : (envAt t 0).loc THRESHOLD ≡ (envAt t 0).pub PI_THRESHOLD [ZMOD 2013265921] := by
      simpa only [c1ThresholdPin, VmConstraint2.holdsAt, holdsVm_piFirst_true] using h
    rw [Int.modEq_iff_dvd] at hm; obtain ⟨k, hk⟩ := hm; omega
  -- C2 fact-commitment PI pin (mod `p`), lifted by canonicality.
  have hc2 : (envAt t 0).loc FACT_COMMITMENT = (envAt t 0).pub PI_FACT_COMMITMENT := by
    have h := hsat.rowConstraints 0 h0 c2FactPin mem_c2
    rw [hfirst] at h
    have hm : (envAt t 0).loc FACT_COMMITMENT ≡ (envAt t 0).pub PI_FACT_COMMITMENT
        [ZMOD 2013265921] := by
      simpa only [c2FactPin, VmConstraint2.holdsAt, holdsVm_piFirst_true] using h
    rw [Int.modEq_iff_dvd] at hm; obtain ⟨k, hk⟩ := hm; omega
  -- C3 slot gate (mod `p`): `SLOT_A ≡ INPUT`; both low-half ⟹ genuine `SLOT_A = INPUT`.
  have hc3 : (envAt t 0).loc SLOT_A = (envAt t 0).loc INPUT := by
    have h := hsat.rowConstraints 0 h0 c3SlotGate mem_c3
    rw [hlast] at h
    simp only [c3SlotGate, VmConstraint2.holdsAt, holdsVm_gate_false] at h
    have hkey : c3Body.eval (envAt t 0).loc
        = (envAt t 0).loc SLOT_A - (envAt t 0).loc INPUT := by
      simp only [c3Body, EmittedExpr.eval]; ring
    rw [hkey, Int.modEq_zero_iff_dvd] at h; obtain ⟨k, hk⟩ := h; omega
  -- C5 diff gate (mod `p`): `DIFF ≡ SLOT_A − THRESHOLD − 1`; `DIFF < 2^29 ⊂ p/2` + low-half
  -- SLOT_A/THRESHOLD make the subtraction wrap-free, so the congruence IS the ℤ identity.
  have hc5 : (envAt t 0).loc DIFF = (envAt t 0).loc SLOT_A - (envAt t 0).loc THRESHOLD - 1 := by
    have h := hsat.rowConstraints 0 h0 c5DiffGate mem_c5
    rw [hlast] at h
    simp only [c5DiffGate, VmConstraint2.holdsAt, holdsVm_gate_false] at h
    have hkey : c5Body.eval (envAt t 0).loc
        = (envAt t 0).loc DIFF - (envAt t 0).loc SLOT_A + (envAt t 0).loc THRESHOLD + 1 := by
      simp only [c5Body, EmittedExpr.eval]; ring
    rw [hkey, Int.modEq_zero_iff_dvd] at h; obtain ⟨k, hk⟩ := h; omega
  exact ⟨by omega, by rw [hpow]; omega, hc2⟩

def rowOf (cols : List ℤ) : Assignment := fun i => cols.getD i 0
def hash0 : List ℤ → ℤ := fun _ => 0

/-- The honest satisfying assignment: `value = 101 > threshold = 40`, `diff = 101−40−1 = 60`. -/
def gtAsg : Assignment := rowOf [101, 101, 40, 60, 0]
def gtPub : Assignment := rowOf [40, 0]
/-- Carries the FAITHFUL range table AND the Poseidon2 chip table with the two genuine `chipRow`s
the weld lookups absorb (arity-7 fact-hash over `INPUT = 101`, arity-4 BLINDED fact-commitment
`[fact_hash, state_root, blinding, 0]`). -/
def gtTf : TraceFamily
  | TableId.range => rangeRows DIFF_BITS
  | TableId.poseidon2 =>
      [chipRow hash0 [0, 101, 0, 0, 0, FACT_MARK, 1] (List.replicate 7 0),
       chipRow hash0 [0, 0, 0, 0] (List.replicate 7 0)]
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
    -- the two weld chip lookups land in the concrete Poseidon2 chip table (decidable membership).
    have gph0 : Lookup.holdsAt gtWitnessTrace.tf (envAt gtWitnessTrace 0)
        ⟨TableId.poseidon2, chipLookupTuple [.var PREDICATE_SYM, .var INPUT, .var TERM1, .var TERM2,
          .const 0, .const FACT_MARK, .const 1] FACT_HASH FACTHASH_LANES⟩ := by
      simp only [Lookup.holdsAt, gtWitnessTrace, gtTf]; decide
    have gph1 : Lookup.holdsAt gtWitnessTrace.tf (envAt gtWitnessTrace 1)
        ⟨TableId.poseidon2, chipLookupTuple [.var PREDICATE_SYM, .var INPUT, .var TERM1, .var TERM2,
          .const 0, .const FACT_MARK, .const 1] FACT_HASH FACTHASH_LANES⟩ := by
      simp only [Lookup.holdsAt, gtWitnessTrace, gtTf]; decide
    have gpc0 : Lookup.holdsAt gtWitnessTrace.tf (envAt gtWitnessTrace 0)
        ⟨TableId.poseidon2, chipLookupTuple [.var FACT_HASH, .var STATE_ROOT, .var BLINDING, .const 0]
          FACT_COMMITMENT FACTCOMMIT_LANES⟩ := by
      simp only [Lookup.holdsAt, gtWitnessTrace, gtTf]; decide
    have gpc1 : Lookup.holdsAt gtWitnessTrace.tf (envAt gtWitnessTrace 1)
        ⟨TableId.poseidon2, chipLookupTuple [.var FACT_HASH, .var STATE_ROOT, .var BLINDING, .const 0]
          FACT_COMMITMENT FACTCOMMIT_LANES⟩ := by
      simp only [Lookup.holdsAt, gtWitnessTrace, gtTf]; decide
    have hi2 : i < 2 := hi
    clear hi
    simp only [predicateGtDesc] at hc
    interval_cases i <;>
      fin_cases hc <;>
      simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm,
        c1ThresholdPin, c2FactPin, c3SlotGate, c5DiffGate, c6RangeLookup,
        factHashLookup, factCommitLookup, g0, g1] <;>
      first
        | exact gl0
        | exact gl1
        | exact gph0
        | exact gph1
        | exact gpc0
        | exact gpc1
        | decide
  rowHashes := by intro i _; trivial
  rowRanges := by intro i _ r hr; simp only [predicateGtDesc, List.not_mem_nil] at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by intro op hop; rw [memLog_pred] at hop; simp at hop
  memDisciplined := by rw [memLog_pred]; trivial
  memBalanced := by rw [memLog_pred]; exact memCheck_nil _ _
  memTableFaithful := by rw [memLog_pred]; rfl
  mapTableFaithful := by rw [mapLog_pred]; rfl

/-- **The canonicality envelope is genuinely INHABITED** on the witness (value `101` / threshold `40`
deep in the low half, diff `60`, commitments `0`) — small canonical field values, so the bridge does
not rest on a vacuous range-check hypothesis. -/
theorem gtWitness_canon : GtCanon gtWitnessTrace := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

theorem gtWitness_sem : ArithGtSem (envAt gtWitnessTrace 0) :=
  predicateGt_sat_imp_sem (t := gtWitnessTrace) gtWitnessTf_range (by decide) gtWitness_canon
    gtWitness_satisfies

theorem gtWitness_sem_concrete :
    (envAt gtWitnessTrace 0).pub PI_THRESHOLD = 40
      ∧ (envAt gtWitnessTrace 0).loc INPUT = 101
      ∧ (envAt gtWitnessTrace 0).pub PI_THRESHOLD < (envAt gtWitnessTrace 0).loc INPUT := by
  refine ⟨by decide, by decide, gtWitness_sem.gt⟩

/-! ## §5b — THE VALUE↔FACT WELD: the committed fact carries the proven value. -/

/-- **`predicateGt_fact_opens_to_input`** — from the two in-circuit Poseidon2 chip lookups (against a
SOUND chip table), the public fact commitment opens to the DOUBLE hash of a fact whose value slot is
the SAME `INPUT` column the comparison is proved about. -/
theorem predicateGt_fact_opens_to_input {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (hlen : 2 ≤ t.rows.length)
    (hcanon : GtCanon t)
    (hsat : Satisfied2 hash predicateGtDesc minit mfin maddrs t) :
    (envAt t 0).pub PI_FACT_COMMITMENT
      = hash [hash [(envAt t 0).loc PREDICATE_SYM, (envAt t 0).loc INPUT,
                    (envAt t 0).loc TERM1, (envAt t 0).loc TERM2, 0, FACT_MARK, 1],
              (envAt t 0).loc STATE_ROOT, (envAt t 0).loc BLINDING, 0] := by
  obtain ⟨_, _, _, ⟨hcF0, hcF1⟩, _, ⟨hcPF0, hcPF1⟩⟩ := hcanon
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
theorem predicateGt_value_forge_rejected {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (hlen : 2 ≤ t.rows.length) (hcanon : GtCanon t) (v0 : ℤ)
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
    ¬ Satisfied2 hash predicateGtDesc minit mfin maddrs t := by
  intro hsat
  have hopen := predicateGt_fact_opens_to_input hChip hlen hcanon hsat
  exact hforge (hinj _ _ (hopen.symm.trans hcred))

/-- The concrete Poseidon2 chip table is genuinely SOUND for `hash0`. -/
theorem gtChipSound : ChipTableSound hash0 (gtWitnessTrace.tf .poseidon2) := by
  intro r hr
  simp only [gtWitnessTrace, gtTf, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h
  · exact ⟨[0, 101, 0, 0, 0, FACT_MARK, 1], List.replicate 7 0, by decide, by decide, h⟩
  · exact ⟨[0, 0, 0, 0], List.replicate 7 0, by decide, by decide, h⟩

/-- **The value↔fact WELD leg FIRES on the witness (non-vacuously).** -/
theorem gtWitness_fact_opens :
    (envAt gtWitnessTrace 0).pub PI_FACT_COMMITMENT
      = hash0 [hash0 [(envAt gtWitnessTrace 0).loc PREDICATE_SYM, (envAt gtWitnessTrace 0).loc INPUT,
                (envAt gtWitnessTrace 0).loc TERM1, (envAt gtWitnessTrace 0).loc TERM2,
                0, FACT_MARK, 1], (envAt gtWitnessTrace 0).loc STATE_ROOT,
                (envAt gtWitnessTrace 0).loc BLINDING, 0] :=
  predicateGt_fact_opens_to_input (t := gtWitnessTrace) gtChipSound (by decide) gtWitness_canon
    gtWitness_satisfies

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
#assert_axioms predicateGt_fact_opens_to_input
#assert_axioms predicateGt_value_forge_rejected
#assert_axioms gtChipSound
#assert_axioms gtWitness_fact_opens
#assert_axioms gtWitness_satisfies
#assert_axioms gtWitness_sem
#assert_axioms gtWitness_sem_concrete
#assert_axioms gtBad_not_satisfies

end Dregg2.Circuit.Emit.PredicatesGtRefine

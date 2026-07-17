/-
# Dregg2.Circuit.Emit.PredicatesLeRefine — Rung-1 (functional correctness) + Rung-2 (no-forgery)
for the emitted `LessThanOrEqual` descriptor `predicateLeDesc`.

## What this file IS

* **§1 `ArithLeSem`** — the authored functional spec: a row witnesses `value ≤ threshold` with a
  bounded gap and a bound fact-commitment.
* **§5 `predicateLe_sat_imp_sem` (RUNG-1)** — a trace SATISFYING `predicateLeDesc` (via the deployed
  `Satisfied2`, against the faithful range table) computes the GENUINE `≤` relation on row 0.
* **§6 non-vacuity** — `leWitness_satisfies` (a concrete `40 ≤ 100` run that PROVABLY satisfies) and
  `leBad_not_satisfies` (RUNG-2 no-forgery: an honest `110 > 100` run — C3/C5 consistent — that
  PROVABLY FAILS because the C6 range tooth rejects its `diff = −10`).

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.PredicatesLeEmit

namespace Dregg2.Circuit.Emit.PredicatesLeRefine

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit
  (VmConstraint VmRowEnv VmRange holdsVm_gate_false holdsVm_piFirst_true)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.PredicatesLeEmit

set_option autoImplicit false
set_option maxRecDepth 8000

/-! ## §1 — the authored functional spec. -/

/-- **`ArithLeSem env`** — the `LessThanOrEqual(value, threshold)` relation over the ℤ field model:
the private input value (`loc INPUT`) is `≤` the PUBLIC threshold (`pub PI_THRESHOLD`), with a gap
inside the honest chip domain `[0, 2^29)`, and the published fact commitment binds its public input. -/
structure ArithLeSem (env : VmRowEnv) : Prop where
  le        : env.loc INPUT ≤ env.pub PI_THRESHOLD
  domain    : env.pub PI_THRESHOLD - env.loc INPUT < (2 : ℤ) ^ DIFF_BITS
  factBinds : env.loc FACT_COMMITMENT = env.pub PI_FACT_COMMITMENT

/-! ## §2 — the constraints are genuinely present. -/

theorem mem_c1 : c1ThresholdPin ∈ predicateLeDesc.constraints :=
  List.mem_cons.mpr (Or.inl rfl)
theorem mem_c2 : c2FactPin ∈ predicateLeDesc.constraints :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
theorem mem_c3 : c3SlotGate ∈ predicateLeDesc.constraints :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))
theorem mem_c5 : c5DiffGate ∈ predicateLeDesc.constraints :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr
    (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))
theorem mem_c6 : c6RangeLookup ∈ predicateLeDesc.constraints :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr
    (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))
theorem mem_factHash : factHashLookup ∈ predicateLeDesc.constraints := by
  simp only [predicateLeDesc]
  apply List.mem_cons_of_mem; apply List.mem_cons_of_mem; apply List.mem_cons_of_mem
  apply List.mem_cons_of_mem; apply List.mem_cons_of_mem; exact List.mem_cons_self
theorem mem_factCommit : factCommitLookup ∈ predicateLeDesc.constraints := by
  simp only [predicateLeDesc]
  apply List.mem_cons_of_mem; apply List.mem_cons_of_mem; apply List.mem_cons_of_mem
  apply List.mem_cons_of_mem; apply List.mem_cons_of_mem; apply List.mem_cons_of_mem
  exact List.mem_cons_self

/-! ## §3 — empty mem/map logs. -/

theorem memOpsOf_pred : memOpsOf predicateLeDesc = [] := rfl
theorem mapOpsOf_pred : mapOpsOf predicateLeDesc = [] := rfl
theorem memLog_pred (t : VmTrace) : memLog predicateLeDesc t = [] := by
  simp [memLog, memOpsOf_pred]
theorem mapLog_pred (t : VmTrace) : mapLog predicateLeDesc t = [] := by
  simp [mapLog, mapOpsOf_pred]

/-! ## §5 — THE WHOLE-DESCRIPTOR BRIDGE (RUNG-1, SAT_IMPLIES_SEM). -/

/-! The deployed range-check canonicality envelope — under the mod-`p` denotation each pin/gate binds
only a congruence; `THRESHOLD`/`INPUT`/`SLOT_A` low-half (`2·x < p`) + canonical commitments/PIs lift
them to the genuine ℤ `≤` relation (`DIFF ∈ [0, 2^29) ⊂ [0, p/2)` from C6 makes `DIFF = THRESHOLD −
SLOT_A` wrap-free). Inhabited by `leWitness_canon`. -/
def LeCanon (t : VmTrace) : Prop :=
  (0 ≤ (envAt t 0).loc INPUT ∧ 2 * (envAt t 0).loc INPUT < 2013265921)
  ∧ (0 ≤ (envAt t 0).loc SLOT_A ∧ 2 * (envAt t 0).loc SLOT_A < 2013265921)
  ∧ (0 ≤ (envAt t 0).loc THRESHOLD ∧ 2 * (envAt t 0).loc THRESHOLD < 2013265921)
  ∧ (0 ≤ (envAt t 0).loc FACT_COMMITMENT ∧ (envAt t 0).loc FACT_COMMITMENT < 2013265921)
  ∧ (0 ≤ (envAt t 0).pub PI_THRESHOLD ∧ (envAt t 0).pub PI_THRESHOLD < 2013265921)
  ∧ (0 ≤ (envAt t 0).pub PI_FACT_COMMITMENT ∧ (envAt t 0).pub PI_FACT_COMMITMENT < 2013265921)

/-- **`predicateLe_sat_imp_sem`.** A trace satisfying `predicateLeDesc` against the faithful range
table computes the genuine `≤` relation on its boundary row `0`. -/
theorem predicateLe_sat_imp_sem {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hrange : t.tf .range = rangeRows DIFF_BITS)
    (hlen : 2 ≤ t.rows.length)
    (hcanon : LeCanon t)
    (hsat : Satisfied2 hash predicateLeDesc minit mfin maddrs t) :
    ArithLeSem (envAt t 0) := by
  obtain ⟨⟨hcI0, hcI1⟩, ⟨hcS0, hcS1⟩, ⟨hcT0, hcT1⟩, ⟨hcF0, hcF1⟩, ⟨hcPT0, hcPT1⟩, ⟨hcPF0, hcPF1⟩⟩ :=
    hcanon
  have h0 : 0 < t.rows.length := by omega
  have hfirst : ((0 : Nat) == 0) = true := rfl
  have hlast : ((0 : Nat) + 1 == t.rows.length) = false := by
    have : (0 : Nat) + 1 ≠ t.rows.length := by omega
    simpa using this
  have hc6 : 0 ≤ (envAt t 0).loc DIFF ∧ (envAt t 0).loc DIFF < (2 : ℤ) ^ DIFF_BITS := by
    have h := hsat.rowConstraints 0 h0 c6RangeLookup mem_c6
    simp only [c6RangeLookup, VmConstraint2.holdsAt] at h
    have hv := lookup_replaces_range DIFF_BITS t.tf hrange (envAt t 0) DIFF h
    simpa only [VmRange.holds] using hv
  obtain ⟨hlo, hhi⟩ := hc6
  have hpow : (2 : ℤ) ^ DIFF_BITS = 536870912 := by norm_num [DIFF_BITS]
  rw [hpow] at hhi
  have hc1 : (envAt t 0).loc THRESHOLD = (envAt t 0).pub PI_THRESHOLD := by
    have h := hsat.rowConstraints 0 h0 c1ThresholdPin mem_c1
    rw [hfirst] at h
    have hm : (envAt t 0).loc THRESHOLD ≡ (envAt t 0).pub PI_THRESHOLD [ZMOD 2013265921] := by
      simpa only [c1ThresholdPin, VmConstraint2.holdsAt, holdsVm_piFirst_true] using h
    rw [Int.modEq_iff_dvd] at hm; obtain ⟨k, hk⟩ := hm; omega
  have hc2 : (envAt t 0).loc FACT_COMMITMENT = (envAt t 0).pub PI_FACT_COMMITMENT := by
    have h := hsat.rowConstraints 0 h0 c2FactPin mem_c2
    rw [hfirst] at h
    have hm : (envAt t 0).loc FACT_COMMITMENT ≡ (envAt t 0).pub PI_FACT_COMMITMENT
        [ZMOD 2013265921] := by
      simpa only [c2FactPin, VmConstraint2.holdsAt, holdsVm_piFirst_true] using h
    rw [Int.modEq_iff_dvd] at hm; obtain ⟨k, hk⟩ := hm; omega
  have hc3 : (envAt t 0).loc SLOT_A = (envAt t 0).loc INPUT := by
    have h := hsat.rowConstraints 0 h0 c3SlotGate mem_c3
    rw [hlast] at h
    simp only [c3SlotGate, VmConstraint2.holdsAt, holdsVm_gate_false, c3Body, EmittedExpr.eval] at h
    rw [Int.modEq_zero_iff_dvd] at h; obtain ⟨k, hk⟩ := h; omega
  have hc5 : (envAt t 0).loc DIFF = (envAt t 0).loc THRESHOLD - (envAt t 0).loc SLOT_A := by
    have h := hsat.rowConstraints 0 h0 c5DiffGate mem_c5
    rw [hlast] at h
    simp only [c5DiffGate, VmConstraint2.holdsAt, holdsVm_gate_false, c5Body, EmittedExpr.eval] at h
    rw [Int.modEq_zero_iff_dvd] at h; obtain ⟨k, hk⟩ := h; omega
  exact ⟨by omega, by rw [hpow]; omega, hc2⟩

/-! ## §6 — non-vacuity: a satisfying witness, an honest above-threshold run that fails. -/

/-- A row from an explicit column-prefix list (off-the-end = 0). -/
def rowOf (cols : List ℤ) : Assignment := fun i => cols.getD i 0

def hash0 : List ℤ → ℤ := fun _ => 0

/-- The honest satisfying assignment: `value = 40 ≤ threshold = 100`, slot-A copies input,
`diff = threshold − value = 60 ∈ [0, 2^29)`. The value↔fact weld columns are `0` (their chip digests
are `hash0 _ = 0`), with `INPUT` feeding the arity-7 fact-hash absorb. -/
def leAsg : Assignment := rowOf [40, 40, 100, 60, 0]

/-- The public inputs: `PI_THRESHOLD = 100`, `PI_FACT_COMMITMENT = 0` (the zero-hash fact commitment). -/
def lePub : Assignment := rowOf [100, 0]

/-- The witness trace family carries the FAITHFUL range table AND the Poseidon2 chip table with the
two genuine `chipRow`s the weld lookups absorb (arity-7 fact-hash over `INPUT = 40`, arity-2
fact-commitment); every other table is empty. -/
def leTf : TraceFamily
  | TableId.range => rangeRows DIFF_BITS
  | TableId.poseidon2 =>
      [chipRow hash0 [0, 40, 0, 0, 0, FACT_MARK, 1] (List.replicate 7 0),
       chipRow hash0 [0, 0, 0, 0] (List.replicate 7 0)]
  | _ => []

def leWitnessTrace : VmTrace := { rows := [leAsg, leAsg], pub := lePub, tf := leTf }

theorem leWitnessTf_range : leWitnessTrace.tf .range = rangeRows DIFF_BITS := by
  simp only [leWitnessTrace, leTf]

/-- **The witness PROVABLY satisfies `predicateLeDesc`.** -/
theorem leWitness_satisfies :
    Satisfied2 hash0 predicateLeDesc (fun _ => 0) (fun _ => (0, 0)) [] leWitnessTrace where
  rowConstraints := by
    intro i hi c hc
    have h60 : ([(60 : ℤ)] : List ℤ) ∈ rangeRows DIFF_BITS :=
      (range_row_mem_iff 60 DIFF_BITS).mpr (by norm_num [DIFF_BITS])
    have g0 : ((0 : Nat) + 1 == leWitnessTrace.rows.length) = false := rfl
    have g1 : ((1 : Nat) + 1 == leWitnessTrace.rows.length) = true := rfl
    have hd0 : (envAt leWitnessTrace 0).loc DIFF = 60 := by decide
    have hd1 : (envAt leWitnessTrace 1).loc DIFF = 60 := by decide
    have gl0 : Lookup.holdsAt leWitnessTrace.tf (envAt leWitnessTrace 0)
        ⟨TableId.range, [.var DIFF]⟩ := by
      simp only [Lookup.holdsAt, List.map_cons, List.map_nil, EmittedExpr.eval, leWitnessTf_range, hd0]
      exact h60
    have gl1 : Lookup.holdsAt leWitnessTrace.tf (envAt leWitnessTrace 1)
        ⟨TableId.range, [.var DIFF]⟩ := by
      simp only [Lookup.holdsAt, List.map_cons, List.map_nil, EmittedExpr.eval, leWitnessTf_range, hd1]
      exact h60
    -- the two weld chip lookups land in the concrete Poseidon2 chip table (decidable membership).
    have gph0 : Lookup.holdsAt leWitnessTrace.tf (envAt leWitnessTrace 0)
        ⟨TableId.poseidon2, chipLookupTuple [.var PREDICATE_SYM, .var INPUT, .var TERM1, .var TERM2,
          .const 0, .const FACT_MARK, .const 1] FACT_HASH FACTHASH_LANES⟩ := by
      simp only [Lookup.holdsAt, leWitnessTrace, leTf]; decide
    have gph1 : Lookup.holdsAt leWitnessTrace.tf (envAt leWitnessTrace 1)
        ⟨TableId.poseidon2, chipLookupTuple [.var PREDICATE_SYM, .var INPUT, .var TERM1, .var TERM2,
          .const 0, .const FACT_MARK, .const 1] FACT_HASH FACTHASH_LANES⟩ := by
      simp only [Lookup.holdsAt, leWitnessTrace, leTf]; decide
    have gpc0 : Lookup.holdsAt leWitnessTrace.tf (envAt leWitnessTrace 0)
        ⟨TableId.poseidon2, chipLookupTuple [.var FACT_HASH, .var STATE_ROOT, .var BLINDING, .const 0]
          FACT_COMMITMENT FACTCOMMIT_LANES⟩ := by
      simp only [Lookup.holdsAt, leWitnessTrace, leTf]; decide
    have gpc1 : Lookup.holdsAt leWitnessTrace.tf (envAt leWitnessTrace 1)
        ⟨TableId.poseidon2, chipLookupTuple [.var FACT_HASH, .var STATE_ROOT, .var BLINDING, .const 0]
          FACT_COMMITMENT FACTCOMMIT_LANES⟩ := by
      simp only [Lookup.holdsAt, leWitnessTrace, leTf]; decide
    have hi2 : i < 2 := hi
    clear hi
    simp only [predicateLeDesc] at hc
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
  rowRanges := by intro i _ r hr; simp only [predicateLeDesc, List.not_mem_nil] at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by intro op hop; rw [memLog_pred] at hop; simp at hop
  memDisciplined := by rw [memLog_pred]; trivial
  memBalanced := by rw [memLog_pred]; exact memCheck_nil _ _
  memTableFaithful := by rw [memLog_pred]; rfl
  mapTableFaithful := by rw [mapLog_pred]; rfl

/-- **The bridge FIRES on the witness (true half of non-vacuity).** -/
theorem leWitness_canon : LeCanon leWitnessTrace := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

theorem leWitness_sem : ArithLeSem (envAt leWitnessTrace 0) :=
  predicateLe_sat_imp_sem (t := leWitnessTrace) leWitnessTf_range (by decide) leWitness_canon
    leWitness_satisfies

/-- The recovered content is the concrete `40 ≤ 100`. -/
theorem leWitness_sem_concrete :
    (envAt leWitnessTrace 0).pub PI_THRESHOLD = 100
      ∧ (envAt leWitnessTrace 0).loc INPUT = 40
      ∧ (envAt leWitnessTrace 0).loc INPUT ≤ (envAt leWitnessTrace 0).pub PI_THRESHOLD := by
  refine ⟨by decide, by decide, leWitness_sem.le⟩

/-! ## §5b — THE VALUE↔FACT WELD (held forgery #2): the committed fact carries the proven value. -/

/-- **`predicateLe_fact_opens_to_input`** — from the two in-circuit Poseidon2 chip lookups (against a
SOUND chip table), the public fact commitment equals the DOUBLE hash of a fact whose value slot is the
SAME `INPUT` column the `≤` relation is proved about. So a satisfying proof cannot name a fact
commitment whose value differs from the value it proves about. -/
theorem predicateLe_fact_opens_to_input {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (hlen : 2 ≤ t.rows.length)
    (hcanon : LeCanon t)
    (hsat : Satisfied2 hash predicateLeDesc minit mfin maddrs t) :
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

/-- **THE WELD BITES (value ≠ committed value ⟹ REJECT).** Under Poseidon2 collision resistance
(injectivity of the fact double-hash in its value slot), a proof whose fact witnesses match a trusted
credential of value `v0` but whose proved `INPUT ≠ v0` CANNOT satisfy the descriptor. -/
theorem predicateLe_value_forge_rejected {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (hlen : 2 ≤ t.rows.length) (hcanon : LeCanon t) (v0 : ℤ)
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
    ¬ Satisfied2 hash predicateLeDesc minit mfin maddrs t := by
  intro hsat
  have hopen := predicateLe_fact_opens_to_input hChip hlen hcanon hsat
  exact hforge (hinj _ _ (hopen.symm.trans hcred))

/-- The concrete Poseidon2 chip table is genuinely SOUND for `hash0` (each row is a real `chipRow`). -/
theorem leChipSound : ChipTableSound hash0 (leWitnessTrace.tf .poseidon2) := by
  intro r hr
  simp only [leWitnessTrace, leTf, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h
  · exact ⟨[0, 40, 0, 0, 0, FACT_MARK, 1], List.replicate 7 0, by decide, by decide, h⟩
  · exact ⟨[0, 0, 0, 0], List.replicate 7 0, by decide, by decide, h⟩

/-- **The value↔fact WELD leg FIRES on the witness (non-vacuously).** -/
theorem leWitness_fact_opens :
    (envAt leWitnessTrace 0).pub PI_FACT_COMMITMENT
      = hash0 [hash0 [(envAt leWitnessTrace 0).loc PREDICATE_SYM, (envAt leWitnessTrace 0).loc INPUT,
                (envAt leWitnessTrace 0).loc TERM1, (envAt leWitnessTrace 0).loc TERM2,
                0, FACT_MARK, 1], (envAt leWitnessTrace 0).loc STATE_ROOT,
                (envAt leWitnessTrace 0).loc BLINDING, 0] :=
  predicateLe_fact_opens_to_input (t := leWitnessTrace) leChipSound (by decide) leWitness_canon
    leWitness_satisfies

/-- The HONEST above-threshold attempt: `value = 110 > threshold = 100`, slot-A copies input, and
the diff is the genuine `threshold − value = −10` (so C3 and C5 both HOLD). Only C6 can reject it. -/
def leBadAsg : Assignment := rowOf [110, 110, 100, -10, 0]

def leBadTrace : VmTrace := { rows := [leBadAsg, leBadAsg], pub := lePub, tf := leTf }

theorem leBadTf_range : leBadTrace.tf .range = rangeRows DIFF_BITS := by
  simp only [leBadTrace, leTf]

/-- **RUNG-2 (no-forgery): the honest above-threshold run PROVABLY FAILS `Satisfied2`.** The C6 range
tooth forces `diff ∈ [0, 2^29)`, but a `value > threshold` diff is `−10 < 0` — UNSAT. -/
theorem leBad_not_satisfies :
    ¬ Satisfied2 hash0 predicateLeDesc (fun _ => 0) (fun _ => (0, 0)) [] leBadTrace := by
  intro h
  have h0 : (0 : Nat) < leBadTrace.rows.length := by decide
  have hrc := h.rowConstraints 0 h0 c6RangeLookup mem_c6
  simp only [c6RangeLookup, VmConstraint2.holdsAt] at hrc
  have hv := lookup_replaces_range DIFF_BITS leBadTrace.tf leBadTf_range (envAt leBadTrace 0) DIFF hrc
  simp only [VmRange.holds] at hv
  have hx : (envAt leBadTrace 0).loc DIFF = -10 := by decide
  rw [hx] at hv
  exact absurd hv.1 (by decide)

/-! ## §7 — axiom tripwires. -/

#assert_axioms predicateLe_sat_imp_sem
#assert_axioms predicateLe_fact_opens_to_input
#assert_axioms predicateLe_value_forge_rejected
#assert_axioms leChipSound
#assert_axioms leWitness_fact_opens
#assert_axioms leWitness_satisfies
#assert_axioms leWitness_sem
#assert_axioms leWitness_sem_concrete
#assert_axioms leBad_not_satisfies

end Dregg2.Circuit.Emit.PredicatesLeRefine

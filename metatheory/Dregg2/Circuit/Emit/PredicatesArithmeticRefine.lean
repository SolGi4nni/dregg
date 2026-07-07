/-
# Dregg2.Circuit.Emit.PredicatesArithmeticRefine — the RUNG-1 functional-correctness refinement for
the emitted arithmetic-predicate descriptor (`predicateGeDesc`).

## What this file IS

`PredicatesArithmeticEmit.lean` proves only PER-GATE faithfulness lemmas (`c3_body_zero_iff`,
`c5_body_zero_iff` — each gate poly = 0 ↔ its local slot/diff identity). This file proves the missing
WHOLE-DESCRIPTOR bridge: a trace SATISFYING the emitted `predicateGeDesc` (via the deployed acceptance
predicate `Satisfied2`) computes the GENUINE `GreaterThanOrEqual(value, threshold)` relation.

## The NO_LEAN case — we author the functional spec, then prove the refinement

No prior Lean model states what this circuit computes, so §1 authors the semantic RELATION `ArithGeSem`
(over the ℤ field model): a row witnesses the relation iff its private input value (column `INPUT`) is
`≥` the PUBLIC threshold (`pub PI_THRESHOLD`), with a difference inside the honest chip domain
`[0, 2^29)` (the range-tooth width — a `value` more than `2^29` above `threshold` is outside the
declared domain), AND the published fact-commitment column binds its public input.

§5's `predicateGe_sat_imp_sem` (SAT_IMPLIES_SEM, the load-bearing soundness direction) composes the five
teeth of `predicateGeDesc` on the boundary/active row `0` of any accepting trace:

| tooth                         | fact forced on row 0                                   |
|-------------------------------|--------------------------------------------------------|
| C1 `.piBinding first`         | `loc THRESHOLD = pub PI_THRESHOLD`                      |
| C2 `.piBinding first`         | `loc FACT_COMMITMENT = pub PI_FACT_COMMITMENT`          |
| C3 `.gate c3Body`             | `loc SLOT_A = loc INPUT`                                |
| C5 `.gate c5Body`             | `loc DIFF = loc SLOT_A − loc THRESHOLD`                 |
| C6 `.lookup ⟨range,[DIFF]⟩`   | `0 ≤ loc DIFF ∧ loc DIFF < 2^29`  (under `hrange`)      |

Chaining: `loc DIFF = loc INPUT − pub PI_THRESHOLD ∈ [0, 2^29)`, i.e. `pub PI_THRESHOLD ≤ loc INPUT`
with a bounded difference — the `≥` predicate. The row-0 boundary is where the `.piBinding first` PI
pins fire (`isFirst`) and the `.gate` teeth are still active (`isLast = false`, guaranteed by the
`2 ≤ height` power-of-two padding the deployed AIR always lays); this is the deployment's own single
logical row (`PredicatesArithmeticEmit` §1).

## The named carrier

The range tooth C6 concludes `loc DIFF ∈ [0, 2^29)` only against the FAITHFUL range table. That table
faithfulness enters as the explicit hypothesis `hrange : t.tf .range = rangeRows DIFF_BITS` — the same
`tf .range = rangeRows bits` carrier `DescriptorIR2.lookup_replaces_range` names, discharged concretely
by the witnesses below (their `tf .range` IS `rangeRows 29`). No crypto carrier is consumed (the family
carries no Poseidon2 site).

## Non-vacuity (the anti-scar)

`geWitnessTrace` (§6): a concrete 2-row run `value=100 ≥ threshold=40` (diff `60`) that PROVABLY
`Satisfied2 predicateGeDesc` against the honest `rangeRows 29` table; feeding it the bridge recovers the
genuine `pub PI_THRESHOLD = 40 ≤ 100 = loc INPUT` (`geWitness_sem` / `geWitness_sem_concrete`).
`geBadTrace`: the HONEST `value=30 < threshold=40` attempt (diff `−10`, C1–C5 all consistent) that
PROVABLY FAILS `Satisfied2` (`geBad_not_satisfies`) — the C6 range tooth rejects a below-threshold diff.
So the `Satisfied2` hypothesis is genuinely inhabited AND constraining.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.PredicatesArithmeticEmit

namespace Dregg2.Circuit.Emit.PredicatesArithmeticRefine

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit
  (VmConstraint VmRowEnv VmRange holdsVm_gate_false holdsVm_piFirst_true)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.PredicatesArithmeticEmit

set_option autoImplicit false
set_option maxRecDepth 8000

/-! ## §1 — The authored functional spec: the GENUINE `GreaterThanOrEqual(value, threshold)` relation. -/

/-- **`ArithGeSem env`** — the semantic relation the arithmetic `GreaterThanOrEqual(value, threshold)`
predicate is meant to compute, over the ℤ field model. A row environment `env` witnesses it iff:

  * `ge`        — the private input value (`loc INPUT`) is `≥` the PUBLIC threshold (`pub PI_THRESHOLD`);
  * `domain`    — the difference lies inside the honest chip domain `[0, 2^29)` (the range-tooth width);
  * `factBinds` — the published fact-commitment column (`loc FACT_COMMITMENT`) binds its public input
    (`pub PI_FACT_COMMITMENT`).

This is the missing Rung-1 functional spec (NO prior Lean model): `predicateGe_sat_imp_sem` proves the
emitted descriptor REFINES it. -/
structure ArithGeSem (env : VmRowEnv) : Prop where
  ge        : env.pub PI_THRESHOLD ≤ env.loc INPUT
  domain    : env.loc INPUT - env.pub PI_THRESHOLD < (2 : ℤ) ^ DIFF_BITS
  factBinds : env.loc FACT_COMMITMENT = env.pub PI_FACT_COMMITMENT

/-! ## §2 — The five constraints of `predicateGeDesc` are genuinely present. -/

theorem mem_c1 : c1ThresholdPin ∈ predicateGeDesc.constraints :=
  List.mem_cons.mpr (Or.inl rfl)

theorem mem_c2 : c2FactPin ∈ predicateGeDesc.constraints :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

theorem mem_c3 : c3SlotGate ∈ predicateGeDesc.constraints :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

theorem mem_c5 : c5DiffGate ∈ predicateGeDesc.constraints :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr
    (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

theorem mem_c6 : c6RangeLookup ∈ predicateGeDesc.constraints :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr
    (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

/-! ## §3 — empty mem/map logs (the descriptor is pure gates + one range lookup). -/

theorem memOpsOf_pred : memOpsOf predicateGeDesc = [] := rfl
theorem mapOpsOf_pred : mapOpsOf predicateGeDesc = [] := rfl
theorem memLog_pred (t : VmTrace) : memLog predicateGeDesc t = [] := by
  simp [memLog, memOpsOf_pred]
theorem mapLog_pred (t : VmTrace) : mapLog predicateGeDesc t = [] := by
  simp [mapLog, mapOpsOf_pred]

/-! ## §5 — THE WHOLE-DESCRIPTOR BRIDGE (SAT_IMPLIES_SEM). -/

/-- **`predicateGe_sat_imp_sem` — the Rung-1 functional-correctness refinement.**

A trace `t` that SATISFIES the emitted descriptor `predicateGeDesc` (via the deployed acceptance
predicate `Satisfied2`), against the faithful range table (`hrange`, the named carrier), and padded to
height `≥ 2` (the always-present power-of-two padding, so row `0` is an active transition row), computes
the GENUINE `GreaterThanOrEqual` relation on its boundary row `0`: the private input value is `≥` the
public threshold, with a bounded difference, and the fact commitment binds its public input.

Composed purely from the five per-gate teeth of `PredicatesArithmeticEmit` + the range-tooth carrier
`lookup_replaces_range`. No crypto carrier is consumed. -/
theorem predicateGe_sat_imp_sem {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hrange : t.tf .range = rangeRows DIFF_BITS)
    (hlen : 2 ≤ t.rows.length)
    (hsat : Satisfied2 hash predicateGeDesc minit mfin maddrs t) :
    ArithGeSem (envAt t 0) := by
  have h0 : 0 < t.rows.length := by omega
  have hfirst : ((0 : Nat) == 0) = true := rfl
  have hlast : ((0 : Nat) + 1 == t.rows.length) = false := by
    have : (0 : Nat) + 1 ≠ t.rows.length := by omega
    simpa using this
  -- C1 : threshold PI pin fires on the first row.
  have hc1 : (envAt t 0).loc THRESHOLD = (envAt t 0).pub PI_THRESHOLD := by
    have h := hsat.rowConstraints 0 h0 c1ThresholdPin mem_c1
    rw [hfirst] at h
    simpa only [c1ThresholdPin, VmConstraint2.holdsAt, holdsVm_piFirst_true] using h
  -- C2 : fact-commitment PI pin fires on the first row.
  have hc2 : (envAt t 0).loc FACT_COMMITMENT = (envAt t 0).pub PI_FACT_COMMITMENT := by
    have h := hsat.rowConstraints 0 h0 c2FactPin mem_c2
    rw [hfirst] at h
    simpa only [c2FactPin, VmConstraint2.holdsAt, holdsVm_piFirst_true] using h
  -- C3 : slot identity (active row, isLast = false).
  have hc3 : (envAt t 0).loc SLOT_A = (envAt t 0).loc INPUT := by
    have h := hsat.rowConstraints 0 h0 c3SlotGate mem_c3
    rw [hlast] at h
    simp only [c3SlotGate, VmConstraint2.holdsAt, holdsVm_gate_false] at h
    exact (c3_body_zero_iff (envAt t 0).loc).mp h
  -- C5 : diff computation (active row).
  have hc5 : (envAt t 0).loc DIFF = (envAt t 0).loc SLOT_A - (envAt t 0).loc THRESHOLD := by
    have h := hsat.rowConstraints 0 h0 c5DiffGate mem_c5
    rw [hlast] at h
    simp only [c5DiffGate, VmConstraint2.holdsAt, holdsVm_gate_false] at h
    exact (c5_body_zero_iff (envAt t 0).loc).mp h
  -- C6 : diff range proof against the faithful range table (the named carrier).
  have hc6 : 0 ≤ (envAt t 0).loc DIFF ∧ (envAt t 0).loc DIFF < (2 : ℤ) ^ DIFF_BITS := by
    have h := hsat.rowConstraints 0 h0 c6RangeLookup mem_c6
    simp only [c6RangeLookup, VmConstraint2.holdsAt] at h
    have hv := lookup_replaces_range DIFF_BITS t.tf hrange (envAt t 0) DIFF h
    simpa only [VmRange.holds] using hv
  obtain ⟨hlo, hhi⟩ := hc6
  exact ⟨by omega, by omega, hc2⟩

/-! ## §6 — Non-vacuity: a concrete satisfying witness, an honest below-threshold run that fails. -/

/-- A row from an explicit column-prefix list (off-the-end = 0). -/
def rowOf (cols : List ℤ) : Assignment := fun i => cols.getD i 0

/-- The honest satisfying assignment: `value = 100 ≥ threshold = 40`, slot-A copies the input, and the
range-proved `diff = value − threshold = 60 ∈ [0, 2^29)`; fact commitment `7`. Columns
`[INPUT, SLOT_A, THRESHOLD, DIFF, FACT_COMMITMENT]`. -/
def geAsg : Assignment := rowOf [100, 100, 40, 60, 7]

/-- The public inputs: `PI_THRESHOLD = 40`, `PI_FACT_COMMITMENT = 7`. -/
def gePub : Assignment := rowOf [40, 7]

/-- The witness trace family carries the FAITHFUL range table `rangeRows 29`; every other table is empty
(no mem/map content). Reused by the below-threshold failing witness. -/
def geTf : TraceFamily
  | TableId.range => rangeRows DIFF_BITS
  | _ => []

/-- The concrete 2-row satisfying run (row 0 active, row 1 the wrap row); both rows carry `geAsg`. -/
def geWitnessTrace : VmTrace := { rows := [geAsg, geAsg], pub := gePub, tf := geTf }

/-- The witness range table IS the faithful `rangeRows DIFF_BITS` — the carrier `hrange` this witness
discharges. PROVEN with `rangeRows` kept OPAQUE (`simp`, never `rfl`/`whnf`), so the 2^29-row table is
never enumerated; and stated at the EXACT `geWitnessTrace.tf .range` head so no `whnf` coercion fires
at the use sites. -/
theorem geWitnessTf_range : geWitnessTrace.tf .range = rangeRows DIFF_BITS := by
  simp only [geWitnessTrace, geTf]

/-- The abstract hash never enters the denotation (no hash sites / map ops), so any value serves. -/
def hash0 : List ℤ → ℤ := fun _ => 0

/-- **The witness PROVABLY satisfies the emitted descriptor.** On both rows the range lookup holds by
`60 ∈ rangeRows 29` (via `range_row_mem_iff`, NOT enumeration); on the active row 0 the two PI pins /
two gates hold, on the wrap row 1 they are vacuous; the memory legs are the empty-log balance. -/
theorem geWitness_satisfies :
    Satisfied2 hash0 predicateGeDesc (fun _ => 0) (fun _ => (0, 0)) [] geWitnessTrace where
  rowConstraints := by
    intro i hi c hc
    have h60 : ([(60 : ℤ)] : List ℤ) ∈ rangeRows DIFF_BITS :=
      (range_row_mem_iff 60 DIFF_BITS).mpr (by norm_num [DIFF_BITS])
    -- the two active/wrap-row guards, as literal Bools (so the `.gate` match collapses under `simp`).
    have g0 : ((0 : Nat) + 1 == geWitnessTrace.rows.length) = false := rfl
    have g1 : ((1 : Nat) + 1 == geWitnessTrace.rows.length) = true := rfl
    have hd0 : (envAt geWitnessTrace 0).loc DIFF = 60 := by decide
    have hd1 : (envAt geWitnessTrace 1).loc DIFF = 60 := by decide
    -- the range lookup holds on each row (via `range_row_mem_iff`, NOT table enumeration).
    have gl0 : Lookup.holdsAt geWitnessTrace.tf (envAt geWitnessTrace 0)
        ⟨TableId.range, [.var DIFF]⟩ := by
      simp only [Lookup.holdsAt, List.map_cons, List.map_nil, EmittedExpr.eval, geWitnessTf_range, hd0]
      exact h60
    have gl1 : Lookup.holdsAt geWitnessTrace.tf (envAt geWitnessTrace 1)
        ⟨TableId.range, [.var DIFF]⟩ := by
      simp only [Lookup.holdsAt, List.map_cons, List.map_nil, EmittedExpr.eval, geWitnessTf_range, hd1]
      exact h60
    have hi2 : i < 2 := hi
    clear hi
    simp only [predicateGeDesc] at hc
    -- the gate / PI-pin teeth reduce by `decide` (concrete trace); the two range lookups by `gl0`/`gl1`.
    interval_cases i <;>
      fin_cases hc <;>
      simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm,
        c1ThresholdPin, c2FactPin, c3SlotGate, c5DiffGate, c6RangeLookup, g0, g1] <;>
      first
        | exact gl0
        | exact gl1
        | decide
  rowHashes := by intro i _; trivial
  rowRanges := by intro i _ r hr; simp only [predicateGeDesc, List.not_mem_nil] at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by intro op hop; rw [memLog_pred] at hop; simp at hop
  memDisciplined := by rw [memLog_pred]; trivial
  memBalanced := by rw [memLog_pred]; exact memCheck_nil _ _
  memTableFaithful := by rw [memLog_pred]; rfl
  mapTableFaithful := by rw [mapLog_pred]; rfl

/-- **The bridge FIRES on the witness (the true half of non-vacuity).** Feeding the concrete satisfying
trace + the faithful range table to `predicateGe_sat_imp_sem` recovers the genuine relation. -/
theorem geWitness_sem : ArithGeSem (envAt geWitnessTrace 0) :=
  predicateGe_sat_imp_sem (t := geWitnessTrace) geWitnessTf_range (by decide) geWitness_satisfies

/-- The recovered semantic content is the concrete, non-trivial `40 ≤ 100` (threshold `≤` value) — not a
`True`/constant conclusion. -/
theorem geWitness_sem_concrete :
    (envAt geWitnessTrace 0).pub PI_THRESHOLD = 40
      ∧ (envAt geWitnessTrace 0).loc INPUT = 100
      ∧ (envAt geWitnessTrace 0).pub PI_THRESHOLD ≤ (envAt geWitnessTrace 0).loc INPUT := by
  refine ⟨by decide, by decide, geWitness_sem.ge⟩

/-- The HONEST below-threshold attempt: `value = 30 < threshold = 40`, slot-A copies the input, and the
diff is the genuine `value − threshold = −10` (so C3 and C5 both HOLD — this is not a malformed trace,
it is an honest prover with a below-threshold value). Only the C6 range tooth can reject it. -/
def geBadAsg : Assignment := rowOf [30, 30, 40, -10, 7]

/-- The below-threshold trace, against the SAME faithful range table `rangeRows 29`. -/
def geBadTrace : VmTrace := { rows := [geBadAsg, geBadAsg], pub := gePub, tf := geTf }

/-- The below-threshold trace's range table is the faithful `rangeRows DIFF_BITS` (opaque `rangeRows`). -/
theorem geBadTf_range : geBadTrace.tf .range = rangeRows DIFF_BITS := by
  simp only [geBadTrace, geTf]

/-- **The honest below-threshold run PROVABLY FAILS the hypothesis (the false half of non-vacuity).**
The C6 range tooth forces `diff ∈ [0, 2^29)`, but the honest diff of a `value < threshold` is `−10 < 0`,
so no `Satisfied2` witness exists — the descriptor's range tooth is exactly what rejects a
below-threshold value. -/
theorem geBad_not_satisfies :
    ¬ Satisfied2 hash0 predicateGeDesc (fun _ => 0) (fun _ => (0, 0)) [] geBadTrace := by
  intro h
  have h0 : (0 : Nat) < geBadTrace.rows.length := by decide
  have hrc := h.rowConstraints 0 h0 c6RangeLookup mem_c6
  simp only [c6RangeLookup, VmConstraint2.holdsAt] at hrc
  have hv := lookup_replaces_range DIFF_BITS geBadTrace.tf geBadTf_range (envAt geBadTrace 0) DIFF hrc
  simp only [VmRange.holds] at hv
  have hx : (envAt geBadTrace 0).loc DIFF = -10 := by decide
  rw [hx] at hv
  exact absurd hv.1 (by decide)

/-! ## §7 — Axiom tripwires. -/

#assert_axioms predicateGe_sat_imp_sem
#assert_axioms geWitness_satisfies
#assert_axioms geWitness_sem
#assert_axioms geWitness_sem_concrete
#assert_axioms geBad_not_satisfies

end Dregg2.Circuit.Emit.PredicatesArithmeticRefine

/-
# Dregg2.Circuit.Emit.BilateralAggregationRung2 — the RUNG-2 discharge of the terminal-cell
no-double-spend obligation for the emitted BILATERAL-AGGREGATION descriptor
(`bilateralAggDescriptor`), and the load-bearing FORGERY that proves it is genuinely needed.

## What Rung 1 left (`BilateralAggregationRefine.lean`)

RUNG 1 proved the whole-descriptor bridge `bilateralAgg_refines : Satisfied2 ∧ nonempty ⟹
BundleAggregated t`, whose crown (CG-4) is the accounting invariant

  * `exactlyOneAgent : prefixSum (isAgentAt t) (last) = 1`   ("exactly one agent cell")
  * `publishedCount  : pub[N_CELLS] = prefixSum (consistentAt t) (last)`.

The security property this family exists for is the CROSS-FEDERATION DOUBLE-SPEND rejection: only ONE
cell across the bundle may claim the acting-agent seat (`multi_cell_cross_fed_binding`). But
`∑ is_agent = 1` is STRICTLY WEAKER than "exactly one cell has the boolean flag `1`", and the gap is
exploitable — because the `is_agent ∈ {0,1}` boolean is a `.base (.gate _)`, DIVIDED BY THE
TRANSITION ZEROFIER, so it is VACUOUS on the last cell (`holdsVm_gate_true`). A prover may therefore
seat TWO genuine agents (`is_agent = 1` on two cells) and absorb the excess in a PHANTOM last cell
carrying `is_agent = -1` (non-boolean, unconstrained): the cumulative still lands at `1`, the trace
`Satisfied2`s, and `exactlyOneAgent` is satisfied by a genuine double-spend. `§4 cheatTrace` /
`cheat_double_spend` exhibit exactly this — the anchor below is LOAD-BEARING, not laundered.

## The residual and its carrier (why this is RUNG2_PARTIAL, not a crypto discharge)

The bilateral-aggregation AIR declares NO tables / hash-sites / ranges / map-ops
(`memOpsOf_agg`/`mapOpsOf_agg = []`): it is CRYPTO-FREE. So — unlike the DFA-routing template, whose
terminal-step residual `hterm` is discharged from the running-hash route-commitment binding under the
`CollisionFree` CR carrier — there is NO crypto carrier here, and NOTHING in `Satisfied2` binds the
last cell's `is_agent` column to any committed reference. The residual is an AIR-COMPLETENESS gap: the
last-row boolean the transition-zerofier lowering drops. Its carrier is therefore the named
hypothesis

  `LastCellAgentBoolean t := isAgentAt t (last) = 0 ∨ isAgentAt t (last) = 1`

— what the EMIT-FIX supplies, NOT a Lean axiom and NOT a crypto primitive. Under it (all non-last
cells are already boolean, forced by the gate off the last row), the genuine

  `UniqueAgent t` — a cell carries the flag `1`, and it is UNIQUE (no two distinct agent cells)

follows unconditionally (`bilateralAgg_rung2`). The carrier is proven load-bearing (the cheat fails it
and fails `UniqueAgent`) and satisfiable (the honest `witTrace` meets it and the discharge FIRES,
`witness_rung2_fires`), so the theorem is non-vacuous.

## The named emit-fix (the one-line additive change that promotes this to RUNG2_PROVED)

Add a LAST-ROW BOOLEAN BOUNDARY for `is_agent` (fires on the last cell, NOT divided by the transition
zerofier) to `EffectVmEmitBilateralAgg.aggConstraints`:

  `.base (.boundary .last (.mul (.var (Agg.schCol Sched.IS_AGENT_CELL))
                                (.add (.var (Agg.schCol Sched.IS_AGENT_CELL)) (.const (-1)))))`

(and the analogous `.boundary .last` boolean for `Agg.CONSISTENT_INDICATOR_COL`, which closes the
symmetric `pub[N_CELLS]` over-count via a phantom `consistent = k>1` last cell). That boundary
DISCHARGES `LastCellAgentBoolean` from `Satisfied2` directly (via `boundaryLast_forces`), at which
point `bilateralAgg_rung2` closes with NO residual. The Rust twin adds the same `when_last_row`
boolean assert; the shape pin `aggConstraints.length == 70` becomes `72`. This file cannot make that
edit (ADDITIVE-ONLY: one new file, no edits to existing ones) — it PROVES the discharge is correct and
NAMES the fix precisely.

## Axiom hygiene / non-vacuity

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}: the residual rides as the NAMED
`LastCellAgentBoolean` hypothesis, never a Lean axiom, and no crypto carrier is needed (crypto-free
family). §4 is the load-bearing cheat (two boolean agents, `Satisfied2`, `∑ = 1`, `¬ UniqueAgent`);
§5 is the firing witness. NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.BilateralAggregationRefine

namespace Dregg2.Circuit.Emit.BilateralAggregationRung2

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRowEnv VmRow)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmitBilateralAgg
open Dregg2.Circuit.Emit.BilateralAggregationRefine

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## §0 — Prefix-sum arithmetic over a NONNEGATIVE contribution column.

The pure integer core: a prefix sum of `{0,1}`-valued (hence nonnegative) terms that lands at `1`
forces EXACTLY ONE term to be `1`. These are the load-bearing lemmas the discharge threads. -/

/-- A prefix sum of nonnegative terms is nonnegative. -/
theorem prefixSum_nonneg (f : Nat → ℤ) :
    ∀ n, (∀ k, k ≤ n → 0 ≤ f k) → 0 ≤ prefixSum f n := by
  intro n
  induction n with
  | zero => intro h; simpa only [prefixSum] using h 0 (le_refl 0)
  | succ m ih =>
      intro h
      simp only [prefixSum]
      have h1 : 0 ≤ prefixSum f m := ih (fun k hk => h k (Nat.le_succ_of_le hk))
      have h2 : 0 ≤ f (m + 1) := h (m + 1) (le_refl _)
      linarith

/-- Any single term is `≤` the whole prefix sum (all terms nonnegative). -/
theorem prefixSum_ge (f : Nat → ℤ) :
    ∀ n, (∀ k, k ≤ n → 0 ≤ f k) → ∀ a, a ≤ n → f a ≤ prefixSum f n := by
  intro n
  induction n with
  | zero =>
      intro _ a ha
      obtain rfl : a = 0 := Nat.le_zero.mp ha
      exact le_of_eq (by simp only [prefixSum])
  | succ m ih =>
      intro h a ha
      simp only [prefixSum]
      have hnnLast : 0 ≤ f (m + 1) := h (m + 1) (le_refl _)
      have hnnPre : 0 ≤ prefixSum f m := prefixSum_nonneg f m (fun k hk => h k (Nat.le_succ_of_le hk))
      by_cases haEq : a = m + 1
      · subst haEq; linarith
      · have ham : a ≤ m := by omega
        have := ih (fun k hk => h k (Nat.le_succ_of_le hk)) a ham
        linarith

/-- A prefix sum of terms that are all `0` is `0`. -/
theorem prefixSum_all_zero (f : Nat → ℤ) :
    ∀ n, (∀ k, k ≤ n → f k = 0) → prefixSum f n = 0 := by
  intro n
  induction n with
  | zero => intro h; simpa only [prefixSum] using h 0 (le_refl 0)
  | succ m ih =>
      intro h
      simp only [prefixSum, ih (fun k hk => h k (Nat.le_succ_of_le hk)), h (m + 1) (le_refl _),
        add_zero]

/-- **Two distinct nonnegative terms sum to `≤` the whole prefix sum.** The tooth that turns "sum is
`1`" into "no two distinct agent cells": two flags equal to `1` would force the sum `≥ 2`. -/
theorem prefixSum_two_le (f : Nat → ℤ) :
    ∀ n, (∀ k, k ≤ n → 0 ≤ f k) → ∀ a b, a ≤ n → b ≤ n → a ≠ b →
      f a + f b ≤ prefixSum f n := by
  intro n
  induction n with
  | zero =>
      intro _ a b ha hb hab
      have ha0 : a = 0 := Nat.le_zero.mp ha
      have hb0 : b = 0 := Nat.le_zero.mp hb
      omega
  | succ m ih =>
      intro h a b ha hb hab
      simp only [prefixSum]
      have hnnLast : 0 ≤ f (m + 1) := h (m + 1) (le_refl _)
      have hnnPre : 0 ≤ prefixSum f m := prefixSum_nonneg f m (fun k hk => h k (Nat.le_succ_of_le hk))
      by_cases haEq : a = m + 1
      · have hbm : b ≤ m := by omega
        have hb' : f b ≤ prefixSum f m :=
          prefixSum_ge f m (fun k hk => h k (Nat.le_succ_of_le hk)) b hbm
        subst haEq; linarith
      · by_cases hbEq : b = m + 1
        · have ham : a ≤ m := by omega
          have ha' : f a ≤ prefixSum f m :=
            prefixSum_ge f m (fun k hk => h k (Nat.le_succ_of_le hk)) a ham
          subst hbEq; linarith
        · have ham : a ≤ m := by omega
          have hbm : b ≤ m := by omega
          have := ih (fun k hk => h k (Nat.le_succ_of_le hk)) a b ham hbm hab
          linarith

/-! ## §1 — The `is_agent` boolean gate is present, and forces `{0,1}` off the last cell. -/

/-- The `is_agent ∈ {0,1}` boolean gate is in the descriptor (head of the CG-4 block). -/
theorem mem_boolGate_isAgent :
    boolGate (Agg.schCol Sched.IS_AGENT_CELL) ∈ bilateralAggDescriptor.constraints := by
  show boolGate (Agg.schCol Sched.IS_AGENT_CELL) ∈ aggConstraints
  unfold aggConstraints
  exact List.mem_append_left _ (List.mem_append_right _ (by simp [List.mem_cons]))

/-! ## §2 — The genuine no-double-spend property + its discharge under the named residual carrier. -/

/-- **`UniqueAgent t`** — the GENUINE no-double-spend property: some cell carries the agent flag `1`,
and it is the ONLY one (no two distinct cells both claim the agent seat). Strictly stronger than the
Rung-1 crown `∑ is_agent = 1`, which a non-boolean phantom last cell can forge (§4). -/
structure UniqueAgent (t : VmTrace) : Prop where
  /-- At least one cell is the acting agent. -/
  exists_agent : ∃ j, j < t.rows.length ∧ isAgentAt t j = 1
  /-- No two distinct cells both claim the agent seat (the double-spend rejection). -/
  unique_agent : ∀ a b, a < t.rows.length → b < t.rows.length →
      isAgentAt t a = 1 → isAgentAt t b = 1 → a = b

section Discharge
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- **The `is_agent` flag is genuinely boolean on every NON-LAST cell** — read off the boolean gate,
which the transition-zerofier lowering enforces exactly off the last row. -/
theorem isAgent_bool_nonlast
    (hsat : Satisfied2 hash bilateralAggDescriptor minit mfin maddrs t)
    {i : Nat} (hi : i < t.rows.length) (hnl : i + 1 ≠ t.rows.length) :
    isAgentAt t i = 0 ∨ isAgentAt t i = 1 := by
  have hmem : VmConstraint2.base (VmConstraint.gate
      (EmittedExpr.mul (.var (Agg.schCol Sched.IS_AGENT_CELL))
        (.add (.var (Agg.schCol Sched.IS_AGENT_CELL)) (.const (-1)))))
      ∈ bilateralAggDescriptor.constraints := mem_boolGate_isAgent
  have h := gate_forces hsat hi hnl hmem
  have h' : isAgentAt t i * (isAgentAt t i + (-1)) = 0 := by
    simpa only [EmittedExpr.eval, isAgentAt, rowAt] using h
  rcases mul_eq_zero.mp h' with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (by linarith)

/-- **Every cell is boolean, given the last-cell residual carrier.** Non-last cells from the gate;
the last cell from `LastCellAgentBoolean` (the carrier the emit-fix supplies). -/
theorem all_isAgent_bool
    (hsat : Satisfied2 hash bilateralAggDescriptor minit mfin maddrs t)
    (hpos : 0 < t.rows.length)
    (hlastBool : isAgentAt t (t.rows.length - 1) = 0 ∨ isAgentAt t (t.rows.length - 1) = 1) :
    ∀ i, i < t.rows.length → isAgentAt t i = 0 ∨ isAgentAt t i = 1 := by
  intro i hi
  by_cases hlast : i = t.rows.length - 1
  · rw [hlast]; exact hlastBool
  · exact isAgent_bool_nonlast hsat hi (by omega)

/-- **`bilateralAgg_rung2` — the terminal-cell no-double-spend obligation is DISCHARGED under the
named `LastCellAgentBoolean` carrier.**

A trace that `Satisfied2`s the emitted `bilateralAggDescriptor`, is non-empty, and whose LAST cell's
`is_agent` flag is boolean (`hlastBool` — the AIR-completeness residual the transition-zerofier
lowering drops, supplied by the named emit-fix; NOT a crypto carrier, this family is crypto-free)
carries EXACTLY ONE agent cell across the whole bundle (`UniqueAgent t`): every cell is boolean (gate
off the last row + the carrier on it), and a prefix sum of `{0,1}`-valued flags landing at `1`
(the Rung-1 crown) forces a UNIQUE `1`. No two federations can both claim the agent seat. -/
theorem bilateralAgg_rung2
    (hsat : Satisfied2 hash bilateralAggDescriptor minit mfin maddrs t)
    (hne : t.rows ≠ [])
    (hlastBool : isAgentAt t (t.rows.length - 1) = 0 ∨ isAgentAt t (t.rows.length - 1) = 1) :
    UniqueAgent t := by
  have hpos : 0 < t.rows.length := List.length_pos_of_ne_nil hne
  have hsum : prefixSum (isAgentAt t) (t.rows.length - 1) = 1 :=
    (bilateralAgg_refines hsat hne).exactlyOneAgent
  have hbool : ∀ i, i < t.rows.length → isAgentAt t i = 0 ∨ isAgentAt t i = 1 :=
    all_isAgent_bool hsat hpos hlastBool
  have hnn : ∀ k, k ≤ t.rows.length - 1 → 0 ≤ isAgentAt t k := by
    intro k hk
    have hk' : k < t.rows.length := by omega
    rcases hbool k hk' with h0 | h1 <;> omega
  refine ⟨?_, ?_⟩
  · -- existence: if no cell is `1`, all are `0`, so the prefix sum is `0 ≠ 1`.
    by_contra hno
    have hall0 : ∀ k, k ≤ t.rows.length - 1 → isAgentAt t k = 0 := by
      intro k hk
      have hk' : k < t.rows.length := by omega
      rcases hbool k hk' with h0 | h1
      · exact h0
      · exact absurd ⟨k, hk', h1⟩ hno
    have hz : prefixSum (isAgentAt t) (t.rows.length - 1) = 0 := prefixSum_all_zero _ _ hall0
    omega
  · -- uniqueness: two distinct agent cells would force the prefix sum `≥ 2`.
    intro a b ha hb hAa hAb
    by_contra hab
    have haL : a ≤ t.rows.length - 1 := by omega
    have hbL : b ≤ t.rows.length - 1 := by omega
    rcases Nat.lt_or_ge a b with hlt | hge
    · have hle := prefixSum_two_le (isAgentAt t) (t.rows.length - 1) hnn a b haL hbL (Nat.ne_of_lt hlt)
      omega
    · have hba : b < a := by omega
      have hle := prefixSum_two_le (isAgentAt t) (t.rows.length - 1) hnn b a hbL haL (Nat.ne_of_lt hba)
      omega

end Discharge

#assert_axioms prefixSum_nonneg
#assert_axioms prefixSum_two_le
#assert_axioms bilateralAgg_rung2

/-! ## §3 — The abstract hash never enters (mirrors the Rung-1 crypto-free note). -/

/-- The abstract hash is irrelevant to this descriptor's denotation (no hash-sites / map-ops). -/
def hash0 : List ℤ → ℤ := fun _ => 0

/-! ## §4 — THE FORGERY (load-bearing anchor): `Satisfied2` alone does NOT force `UniqueAgent`.

A 3-cell bundle with TWO genuine agent cells (cells 0 and 1, `is_agent = 1`) and a PHANTOM last cell
carrying `is_agent = -1` (non-boolean — the last-row boolean gate is vacuous). It PROVABLY
`Satisfied2`s, and its Rung-1 crown `∑ is_agent = 1 + 1 + (-1) = 1` holds, yet TWO federations seat the
agent: a genuine cross-federation double-spend. So the last-cell-boolean carrier is genuinely
load-bearing — the conclusion is impossible from `Satisfied2` + the Rung-1 crown alone. -/

/-- Cheat cell 0: a GENUINE agent cell (`is_agent=1`, `cum=1`, `consistent=1`, `n=1`). -/
def cwr0 : Assignment :=
  fun j => if j = 48 then 1 else if j = 84 then 1 else if j = 85 then 1 else if j = 86 then 1 else 0
/-- Cheat cell 1: a SECOND genuine agent cell (`is_agent=1`, `cum=2`, `consistent=1`, `n=2`). -/
def cwr1 : Assignment :=
  fun j => if j = 48 then 1 else if j = 84 then 2 else if j = 85 then 1 else if j = 86 then 2 else 0
/-- Cheat cell 2 (the LAST cell): the PHANTOM anti-agent `is_agent = -1` (non-boolean, escapes the
vacuous last-row gate), `cum=1`, `consistent=1`, `n=3`. -/
def cwr2 : Assignment :=
  fun j => if j = 48 then -1 else if j = 84 then 1 else if j = 85 then 1 else if j = 86 then 3 else 0
/-- Public inputs pinning the forged `pi[N_CELLS] = 3`. -/
def cpub : Assignment := fun j => if j = 21 then 3 else 0
/-- The cheating 3-cell bundle: two genuine agents + a phantom last cell. -/
def cheatTrace : VmTrace := { rows := [cwr0, cwr1, cwr2], pub := cpub, tf := fun _ => [] }

/-- **The cheat PROVABLY `Satisfied2`s.** The two boolean gates / padding / CG-3 replay are vacuous
on the phantom last row; the cumulative windows thread `1 → 2 → 1`; the boundaries pin `cum = 1` and
`n = pi[N_CELLS] = 3`; CG-2 turn-id agrees (all `0`). -/
theorem cheatTrace_satisfies :
    Satisfied2 hash0 bilateralAggDescriptor (fun _ => 0) (fun _ => (0, 0)) [] cheatTrace where
  rowConstraints := by
    intro i hi c hc
    have hi3 : i < 3 := hi
    rw [show cheatTrace.rows.length = 3 from rfl]
    simp only [bilateralAggDescriptor] at hc
    interval_cases i <;>
      fin_cases hc <;>
      simp only [cg2PiBind, cg3Eq, colEqCol, boolGate, paddingGate, cumAgentTransition,
        cumActiveTransition, firstCumSeed, firstNSeed, lastCumIsOne, lastNEqPi,
        VmConstraint2.holdsAt, VmConstraint.holdsVm, WindowConstraint.holdsAt,
        cheatTrace, envAt, cwr0, cwr1, cwr2, cpub, EmittedExpr.eval, WindowExpr.eval,
        Nat.reduceAdd, Nat.reduceBEq, reduceIte, reduceCtorEq] <;>
      decide
  rowHashes := by intro i _; trivial
  rowRanges := by intro i _ r hr; simp only [bilateralAggDescriptor, List.not_mem_nil] at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by rw [memLog_agg]; simp
  memDisciplined := by rw [memLog_agg]; trivial
  memBalanced := by rw [memLog_agg]; exact memCheck_nil _ _
  memTableFaithful := by rw [memLog_agg]; rfl
  mapTableFaithful := by rw [mapLog_agg]; rfl

/-- The cheat is a genuine `BundleAggregated` (the Rung-1 crown fires on it). -/
theorem cheat_aggregated : BundleAggregated cheatTrace :=
  bilateralAgg_refines cheatTrace_satisfies (by decide)

/-- **THE FORGERY.** Cells 0 and 1 are BOTH genuine agents (`is_agent = 1`), the Rung-1 crown
`∑ is_agent = 1` holds, yet `UniqueAgent cheatTrace` is FALSE — so `Satisfied2` + the Rung-1 crown do
NOT imply the genuine no-double-spend property. The `LastCellAgentBoolean` carrier of
`bilateralAgg_rung2` is genuinely load-bearing (the cheat's last cell carries `is_agent = -1`, failing
it), not laundered. -/
theorem cheat_double_spend :
    isAgentAt cheatTrace 0 = 1 ∧ isAgentAt cheatTrace 1 = 1
    ∧ prefixSum (isAgentAt cheatTrace) (cheatTrace.rows.length - 1) = 1
    ∧ isAgentAt cheatTrace (cheatTrace.rows.length - 1) = -1
    ∧ ¬ UniqueAgent cheatTrace := by
  refine ⟨by decide, by decide, cheat_aggregated.exactlyOneAgent, by decide, ?_⟩
  intro hu
  have h01 : (0 : Nat) = 1 :=
    hu.unique_agent 0 1 (by decide) (by decide) (by decide) (by decide)
  exact absurd h01 (by decide)

/-! ## §5 — Non-vacuity (TRUE half): the discharge FIRES on the honest witness.

The Rung-1 `witTrace` (cell 0 non-agent · cell 1 the agent) has a boolean last cell (`is_agent = 1`),
so `LastCellAgentBoolean` holds and `bilateralAgg_rung2` recovers `UniqueAgent` — the unique agent is
cell 1. The hypothesis set is jointly satisfiable and the discharged conclusion is achievably true. -/

/-- The honest witness's last cell IS boolean (`is_agent = 1`) — the carrier is met. -/
theorem witness_lastBool :
    isAgentAt witTrace (witTrace.rows.length - 1) = 0
    ∨ isAgentAt witTrace (witTrace.rows.length - 1) = 1 :=
  Or.inr (by decide)

/-- **THE RUNG-2 DISCHARGE FIRES on the genuine witness.** Feeding the concrete satisfying `witTrace`
and its met carrier to `bilateralAgg_rung2` recovers `UniqueAgent witTrace`. -/
theorem witness_rung2_fires : UniqueAgent witTrace :=
  bilateralAgg_rung2 witTrace_satisfies (by decide) witness_lastBool

/-- The recovered unique agent is cell 1 (the genuine agent cell), and it is the ONLY one — a real
"exactly one agent" conclusion, not vacuous. -/
theorem witness_value :
    isAgentAt witTrace 1 = 1
    ∧ ∀ a, a < witTrace.rows.length → isAgentAt witTrace a = 1 → a = 1 := by
  refine ⟨by decide, fun a ha hA => ?_⟩
  exact witness_rung2_fires.unique_agent a 1 ha (by decide) hA (by decide)

/-! ## §6 — Axiom tripwires. -/

#assert_axioms cheatTrace_satisfies
#assert_axioms cheat_double_spend
#assert_axioms witness_rung2_fires
#assert_axioms witness_value

end Dregg2.Circuit.Emit.BilateralAggregationRung2

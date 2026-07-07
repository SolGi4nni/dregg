/-
# Dregg2.Circuit.Emit.BilateralAggregationRefine — the RUNG-1 functional-correctness refinement for
the emitted BILATERAL-BUNDLE AGGREGATION descriptor (`bilateralAggDescriptor`).

## What this file IS

`EffectVmEmitBilateralAgg.lean` / `BilateralAggregationEmit.lean` prove only PER-GATE faithfulness
(`cg3_body_zero_iff` — one gate poly = 0 ↔ its LOCAL relation — plus the boundary/identity teeth
`agg_rejects_turn_mismatch` / `agg_rejects_bad_agent_count` over the per-window `aggWindowHolds`).
This file proves the missing WHOLE-DESCRIPTOR bridge: a trace SATISFYING the emitted descriptor via
the DEPLOYED acceptance predicate `DescriptorIR2.Satisfied2` corresponds to the GENUINE semantic
relation the aggregation AIR is meant to compute — a valid bilateral-bundle aggregation:

  * (CG-2 turn binding) the bundle's FIRST and LAST cell carry the published outer-PI turn identity;
  * (CG-3 schedule replay) every NON-FINAL cell's carried counts/roots equal its `expected_*` columns
    (the CG-3 gate is a `when_transition` gate — its faithful Lean denotation `.base (.gate _)` is
    vacuous on the last row, the transition-zerofier lowering, so replay is stated on cells `0…n-2`);
  * (CG-4 accounting — THE CROWN) EXACTLY ONE agent cell across the whole bundle
    (`∑ is_agent = 1`), and the published `n_cells` equals the number of consistent cells
    (`pi[N_CELLS] = ∑ consistent`) — both proven by threading the two cumulative-sum `windowGate`
    recurrences from the row-0 seeds to the last-row boundaries (the running-sum induction
    `running_sum`, the genuine "aggregation" content).

## The semantic relation

No separate whole-trace semantic MODEL existed for this family (the census `lean_spec` is the emit
files themselves); so we AUTHOR the functional spec `BundleAggregated t` (§2) and prove
`Satisfied2 … → BundleAggregated t` (SAT_IMPLIES_SEM) in `bilateralAgg_refines` (§5).

## Non-vacuity

`witTrace` (§6): a concrete 2-row bundle `cell0 (non-agent, consistent) · cell1 (the agent cell)`
that PROVABLY `Satisfied2 bilateralAggDescriptor` — feeding it the bridge recovers the genuine
aggregation (`∑ is_agent = 1`, `pi[N_CELLS] = 2 = ∑ consistent`), exercising BOTH cumulative
recurrences and the schedule replay on the non-last cell. `badTrace`: a trace whose last-row
cumulative ≠ 1 that PROVABLY fails `Satisfied2` (`badTrace_not_satisfied` — the single-agent boundary
bites). So the `Satisfied2` hypothesis is genuinely inhabited AND constraining.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. The bridge is CRYPTO-FREE: the
descriptor declares no tables/hash-sites/ranges/map-ops, so no Poseidon2 carrier enters. NEW file;
imports read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitBilateralAgg

namespace Dregg2.Circuit.Emit.BilateralAggregationRefine

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
  (VmConstraint VmRowEnv VmRow holdsVm_boundaryFirst_true holdsVm_boundaryLast_true
   holdsVm_piFirst_true holdsVm_piLast_true)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmitBilateralAgg

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## §0 — The running (prefix) sum and its determination from a seed + step recurrence. -/

/-- The prefix sum `f 0 + f 1 + … + f n` (the sum of the first `n+1` terms). -/
def prefixSum (f : Nat → ℤ) : Nat → ℤ
  | 0     => f 0
  | n + 1 => prefixSum f n + f (n + 1)

/-- **A cumulative column that is SEEDED (`cumf 0 = contribf 0`) and STEPPED
(`cumf (i+1) = cumf i + contribf (i+1)` on every transition) equals the prefix sum of its
contributions.** The pure arithmetic core of the aggregation crown — a running-sum induction. -/
theorem running_sum (len : Nat) (cumf contribf : Nat → ℤ)
    (hseed : cumf 0 = contribf 0)
    (hstep : ∀ i, i + 1 < len → cumf (i + 1) = cumf i + contribf (i + 1)) :
    ∀ j, j < len → cumf j = prefixSum contribf j := by
  intro j
  induction j with
  | zero => intro _; simpa only [prefixSum] using hseed
  | succ n ih =>
      intro hlt
      have hn : n < len := by omega
      simp only [prefixSum]
      rw [hstep n hlt, ih hn]

/-! ## §1 — Row accessors (the `loc` environment of each trace row). -/

/-- Row `i`'s assignment (the current-row `loc` slice of the row window at `i`). -/
def rowAt (t : VmTrace) (i : Nat) : Assignment := (envAt t i).loc

/-- The agent-cell flag of row `i`. -/
def isAgentAt (t : VmTrace) (i : Nat) : ℤ := rowAt t i (Agg.schCol Sched.IS_AGENT_CELL)
/-- The per-row consistency indicator of row `i`. -/
def consistentAt (t : VmTrace) (i : Nat) : ℤ := rowAt t i Agg.CONSISTENT_INDICATOR_COL
/-- The running `is_agent` cumulative at row `i`. -/
def cumAt (t : VmTrace) (i : Nat) : ℤ := rowAt t i Agg.IS_AGENT_CUMULATIVE_COL
/-- The running active-cell counter at row `i`. -/
def nActiveAt (t : VmTrace) (i : Nat) : ℤ := rowAt t i Agg.N_CELLS_ACTIVE_COL

/-! ## §2 — The GENUINE semantic relation: a valid bilateral-bundle aggregation. -/

/-- **`BundleAggregated t`** — what an accepting bilateral-aggregation trace MEANS: the bundle's cells
share the published turn identity (bound at both ends), each non-final cell faithfully replays its
bilateral schedule, EXACTLY ONE cell is the agent cell across the bundle, and the published
`n_cells` equals the number of consistent cells. This is the functional-correctness spec the emitted
descriptor is proven to refine. -/
structure BundleAggregated (t : VmTrace) : Prop where
  /-- The bundle is non-empty. -/
  nonempty : 0 < t.rows.length
  -- CG-2: the FIRST cell carries the published turn identity (13 felts: turn-hash · effects-hash ·
  -- actor-nonce · previous-receipt).
  turnHashFirst : ∀ i < OuterPi.TURN_HASH_LEN,
      rowAt t 0 (Agg.schCol (Sched.TURN_HASH_BASE + i)) = t.pub (OuterPi.TURN_HASH_BASE + i)
  effectsFirst : ∀ i < OuterPi.EFFECTS_HASH_GLOBAL_LEN,
      rowAt t 0 (Agg.schCol (Sched.EFFECTS_HASH_GLOBAL_BASE + i))
        = t.pub (OuterPi.EFFECTS_HASH_GLOBAL_BASE + i)
  actorNonceFirst : rowAt t 0 (Agg.schCol Sched.ACTOR_NONCE) = t.pub OuterPi.ACTOR_NONCE
  prevReceiptFirst : ∀ i < OuterPi.PREVIOUS_RECEIPT_HASH_LEN,
      rowAt t 0 (Agg.schCol (Sched.PREVIOUS_RECEIPT_HASH_BASE + i))
        = t.pub (OuterPi.PREVIOUS_RECEIPT_HASH_BASE + i)
  -- CG-2: the LAST cell carries the SAME published turn identity.
  turnHashLast : ∀ i < OuterPi.TURN_HASH_LEN,
      rowAt t (t.rows.length - 1) (Agg.schCol (Sched.TURN_HASH_BASE + i))
        = t.pub (OuterPi.TURN_HASH_BASE + i)
  effectsLast : ∀ i < OuterPi.EFFECTS_HASH_GLOBAL_LEN,
      rowAt t (t.rows.length - 1) (Agg.schCol (Sched.EFFECTS_HASH_GLOBAL_BASE + i))
        = t.pub (OuterPi.EFFECTS_HASH_GLOBAL_BASE + i)
  actorNonceLast : rowAt t (t.rows.length - 1) (Agg.schCol Sched.ACTOR_NONCE) = t.pub OuterPi.ACTOR_NONCE
  prevReceiptLast : ∀ i < OuterPi.PREVIOUS_RECEIPT_HASH_LEN,
      rowAt t (t.rows.length - 1) (Agg.schCol (Sched.PREVIOUS_RECEIPT_HASH_BASE + i))
        = t.pub (OuterPi.PREVIOUS_RECEIPT_HASH_BASE + i)
  -- CG-3: every NON-FINAL cell replays its schedule (7 counts + 28 root felts) against the
  -- prover-populated `expected_*` columns.
  replayCounts : ∀ i, i + 1 < t.rows.length → ∀ k < Sched.COUNTS_LEN,
      rowAt t i (Agg.schCol (Sched.COUNTS_BASE + k)) = rowAt t i (Agg.EXPECTED_COUNTS_BASE + k)
  replayRoots : ∀ i, i + 1 < t.rows.length → ∀ k < Sched.ROOTS_LEN,
      rowAt t i (Agg.schCol (Sched.ROOTS_BASE + k)) = rowAt t i (Agg.EXPECTED_ROOTS_BASE + k)
  -- CG-4 (the crown): exactly ONE agent cell across the bundle; published n_cells = # consistent.
  exactlyOneAgent : prefixSum (isAgentAt t) (t.rows.length - 1) = 1
  publishedCount : t.pub OuterPi.N_CELLS = prefixSum (consistentAt t) (t.rows.length - 1)

/-! ## §3 — The consumed constraints are genuinely present in the descriptor. -/

theorem mem_firstCumSeed : firstCumSeed ∈ bilateralAggDescriptor.constraints := by
  show firstCumSeed ∈ aggConstraints; unfold aggConstraints
  exact List.mem_append_right _ (by simp [List.mem_cons])

theorem mem_firstNSeed : firstNSeed ∈ bilateralAggDescriptor.constraints := by
  show firstNSeed ∈ aggConstraints; unfold aggConstraints
  exact List.mem_append_right _ (by simp [List.mem_cons])

theorem mem_lastCumIsOne : lastCumIsOne ∈ bilateralAggDescriptor.constraints := by
  show lastCumIsOne ∈ aggConstraints; unfold aggConstraints
  exact List.mem_append_right _ (by simp [List.mem_cons])

theorem mem_lastNEqPi : lastNEqPi ∈ bilateralAggDescriptor.constraints := by
  show lastNEqPi ∈ aggConstraints; unfold aggConstraints
  exact List.mem_append_right _ (by simp [List.mem_cons])

theorem mem_cumAgentTransition : cumAgentTransition ∈ bilateralAggDescriptor.constraints := by
  show cumAgentTransition ∈ aggConstraints; unfold aggConstraints
  exact List.mem_append_left _ (List.mem_append_right _ (by simp [List.mem_cons]))

theorem mem_cumActiveTransition : cumActiveTransition ∈ bilateralAggDescriptor.constraints := by
  show cumActiveTransition ∈ aggConstraints; unfold aggConstraints
  exact List.mem_append_left _ (List.mem_append_right _ (by simp [List.mem_cons]))

theorem mem_scheduleReplay_counts (k : Nat) (hk : k < Sched.COUNTS_LEN) :
    cg3Eq (Agg.schCol (Sched.COUNTS_BASE + k)) (Agg.EXPECTED_COUNTS_BASE + k)
      ∈ bilateralAggDescriptor.constraints := by
  show _ ∈ aggConstraints; unfold aggConstraints
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
  unfold scheduleReplay
  exact List.mem_append_left _ (List.mem_map_of_mem (List.mem_range.mpr hk))

theorem mem_scheduleReplay_roots (k : Nat) (hk : k < Sched.ROOTS_LEN) :
    cg3Eq (Agg.schCol (Sched.ROOTS_BASE + k)) (Agg.EXPECTED_ROOTS_BASE + k)
      ∈ bilateralAggDescriptor.constraints := by
  show _ ∈ aggConstraints; unfold aggConstraints
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
  unfold scheduleReplay
  exact List.mem_append_right _ (List.mem_map_of_mem (List.mem_range.mpr hk))

/-- A first-row turn binding is in `turnIdBindings .first`; a last-row one in `turnIdBindings .last`. -/
theorem mem_A {c : VmConstraint2} (h : c ∈ turnIdBindings .first) :
    c ∈ bilateralAggDescriptor.constraints := by
  show c ∈ aggConstraints; unfold aggConstraints
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ h)))

theorem mem_B {c : VmConstraint2} (h : c ∈ turnIdBindings .last) :
    c ∈ bilateralAggDescriptor.constraints := by
  show c ∈ aggConstraints; unfold aggConstraints
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ h)))

theorem mem_turn_hash (row : VmRow) (i : Nat) (hi : i < OuterPi.TURN_HASH_LEN) :
    cg2PiBind row (Agg.schCol (Sched.TURN_HASH_BASE + i)) (OuterPi.TURN_HASH_BASE + i)
      ∈ turnIdBindings row := by
  unfold turnIdBindings
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_map_of_mem (List.mem_range.mpr hi))))

theorem mem_turn_effects (row : VmRow) (i : Nat) (hi : i < OuterPi.EFFECTS_HASH_GLOBAL_LEN) :
    cg2PiBind row (Agg.schCol (Sched.EFFECTS_HASH_GLOBAL_BASE + i))
        (OuterPi.EFFECTS_HASH_GLOBAL_BASE + i) ∈ turnIdBindings row := by
  unfold turnIdBindings
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_map_of_mem (List.mem_range.mpr hi))))

theorem mem_turn_nonce (row : VmRow) :
    cg2PiBind row (Agg.schCol Sched.ACTOR_NONCE) OuterPi.ACTOR_NONCE ∈ turnIdBindings row := by
  unfold turnIdBindings
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))

theorem mem_turn_prev (row : VmRow) (i : Nat) (hi : i < OuterPi.PREVIOUS_RECEIPT_HASH_LEN) :
    cg2PiBind row (Agg.schCol (Sched.PREVIOUS_RECEIPT_HASH_BASE + i))
        (OuterPi.PREVIOUS_RECEIPT_HASH_BASE + i) ∈ turnIdBindings row := by
  unfold turnIdBindings
  exact List.mem_append_right _ (List.mem_map_of_mem (List.mem_range.mpr hi))

/-! ## §4 — Extraction: read the per-row facts out of a `Satisfied2` witness. -/

section Extract

variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- **A base-gate constraint forces its body to vanish on a NON-LAST row** (a `.gate` is vacuous on
the last row — the transition-zerofier lowering). -/
theorem gate_forces (hsat : Satisfied2 hash bilateralAggDescriptor minit mfin maddrs t) {i : Nat}
    (hi : i < t.rows.length) (hnl : i + 1 ≠ t.rows.length)
    {g : EmittedExpr} (hg : VmConstraint2.base (.gate g) ∈ bilateralAggDescriptor.constraints) :
    g.eval (envAt t i).loc = 0 := by
  have hrc := hsat.rowConstraints i hi _ hg
  have hlf : (i + 1 == t.rows.length) = false := by simpa using hnl
  simpa only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlf] using hrc

/-- **An `onTransition` window constraint forces its body to vanish on a NON-LAST row.** -/
theorem window_forces (hsat : Satisfied2 hash bilateralAggDescriptor minit mfin maddrs t) {i : Nat}
    (hi : i < t.rows.length) (hnl : i + 1 ≠ t.rows.length)
    {w : WindowConstraint} (hw : VmConstraint2.windowGate w ∈ bilateralAggDescriptor.constraints)
    (honT : w.onTransition = true) :
    w.body.eval (envAt t i) = 0 := by
  have hrc := hsat.rowConstraints i hi _ hw
  have hlf : (i + 1 == t.rows.length) = false := by simpa using hnl
  simp only [VmConstraint2.holdsAt, WindowConstraint.holdsAt, honT, if_true] at hrc
  exact hrc hlf

/-- **A first-row PI binding fires on the first row.** -/
theorem piFirst_forces (hsat : Satisfied2 hash bilateralAggDescriptor minit mfin maddrs t)
    (hpos : 0 < t.rows.length) {col k : Nat}
    (hb : VmConstraint2.base (.piBinding .first col k) ∈ bilateralAggDescriptor.constraints) :
    (envAt t 0).loc col = t.pub k := by
  have hrc := hsat.rowConstraints 0 hpos _ hb
  exact (holdsVm_piFirst_true (envAt t 0) (0 + 1 == t.rows.length) col k).mp hrc

/-- **A last-row PI binding fires on the last row.** -/
theorem piLast_forces (hsat : Satisfied2 hash bilateralAggDescriptor minit mfin maddrs t)
    (hpos : 0 < t.rows.length) {col k : Nat}
    (hb : VmConstraint2.base (.piBinding .last col k) ∈ bilateralAggDescriptor.constraints) :
    (envAt t (t.rows.length - 1)).loc col = t.pub k := by
  have hlt : t.rows.length - 1 < t.rows.length := Nat.sub_lt hpos Nat.one_pos
  have hrc := hsat.rowConstraints (t.rows.length - 1) hlt _ hb
  have hlast_true : (t.rows.length - 1 + 1 == t.rows.length) = true := by
    rw [Nat.sub_add_cancel hpos]; exact beq_self_eq_true _
  rw [hlast_true] at hrc
  exact (holdsVm_piLast_true (envAt t (t.rows.length - 1)) (t.rows.length - 1 == 0) col k).mp hrc

/-- **A first-row boundary forces its body to vanish on the first row.** -/
theorem boundaryFirst_forces (hsat : Satisfied2 hash bilateralAggDescriptor minit mfin maddrs t)
    (hpos : 0 < t.rows.length) {b : EmittedExpr}
    (hb : VmConstraint2.base (.boundary .first b) ∈ bilateralAggDescriptor.constraints) :
    b.eval (envAt t 0).loc = 0 := by
  have hrc := hsat.rowConstraints 0 hpos _ hb
  exact (holdsVm_boundaryFirst_true (envAt t 0) (0 + 1 == t.rows.length) b).mp hrc

/-- **A last-row boundary forces its body to vanish on the last row.** -/
theorem boundaryLast_forces (hsat : Satisfied2 hash bilateralAggDescriptor minit mfin maddrs t)
    (hpos : 0 < t.rows.length) {b : EmittedExpr}
    (hb : VmConstraint2.base (.boundary .last b) ∈ bilateralAggDescriptor.constraints) :
    b.eval (envAt t (t.rows.length - 1)).loc = 0 := by
  have hlt : t.rows.length - 1 < t.rows.length := Nat.sub_lt hpos Nat.one_pos
  have hrc := hsat.rowConstraints (t.rows.length - 1) hlt _ hb
  have hlast_true : (t.rows.length - 1 + 1 == t.rows.length) = true := by
    rw [Nat.sub_add_cancel hpos]; exact beq_self_eq_true _
  rw [hlast_true] at hrc
  exact (holdsVm_boundaryLast_true (envAt t (t.rows.length - 1)) (t.rows.length - 1 == 0) b).mp hrc

/-- Row-0 seed: `cum = is_agent`. -/
theorem seed_cum (hsat : Satisfied2 hash bilateralAggDescriptor minit mfin maddrs t)
    (hpos : 0 < t.rows.length) : cumAt t 0 = isAgentAt t 0 := by
  have h := boundaryFirst_forces hsat hpos mem_firstCumSeed
  simp only [firstCumSeed, EmittedExpr.eval, cumAt, isAgentAt, rowAt] at h ⊢
  omega

/-- Row-0 seed: `n = consistent`. -/
theorem seed_n (hsat : Satisfied2 hash bilateralAggDescriptor minit mfin maddrs t)
    (hpos : 0 < t.rows.length) : nActiveAt t 0 = consistentAt t 0 := by
  have h := boundaryFirst_forces hsat hpos mem_firstNSeed
  simp only [firstNSeed, EmittedExpr.eval, nActiveAt, consistentAt, rowAt] at h ⊢
  omega

/-- Transition: `cum (i+1) = cum i + is_agent (i+1)` (the `is_agent` cumulative recurrence). -/
theorem step_cum (hsat : Satisfied2 hash bilateralAggDescriptor minit mfin maddrs t) (i : Nat)
    (hii : i + 1 < t.rows.length) : cumAt t (i + 1) = cumAt t i + isAgentAt t (i + 1) := by
  have hi : i < t.rows.length := by omega
  have hnl : i + 1 ≠ t.rows.length := by omega
  have h := window_forces hsat hi hnl mem_cumAgentTransition rfl
  simp only [cumAgentTransition, WindowExpr.eval, cumAt, isAgentAt, rowAt, envAt] at h ⊢
  omega

/-- Transition: `n (i+1) = n i + consistent (i+1)` (the active-cell recurrence). -/
theorem step_n (hsat : Satisfied2 hash bilateralAggDescriptor minit mfin maddrs t) (i : Nat)
    (hii : i + 1 < t.rows.length) : nActiveAt t (i + 1) = nActiveAt t i + consistentAt t (i + 1) := by
  have hi : i < t.rows.length := by omega
  have hnl : i + 1 ≠ t.rows.length := by omega
  have h := window_forces hsat hi hnl mem_cumActiveTransition rfl
  simp only [cumActiveTransition, WindowExpr.eval, nActiveAt, consistentAt, rowAt, envAt] at h ⊢
  omega

/-- Last-row boundary: `cum = 1` (exactly one agent cell across the bundle). -/
theorem last_cum (hsat : Satisfied2 hash bilateralAggDescriptor minit mfin maddrs t)
    (hpos : 0 < t.rows.length) : cumAt t (t.rows.length - 1) = 1 := by
  have h := boundaryLast_forces hsat hpos mem_lastCumIsOne
  simp only [lastCumIsOne, EmittedExpr.eval, cumAt, rowAt] at h ⊢
  omega

/-- Last-row binding: `n = pi[N_CELLS]` (the published active-cell count). -/
theorem last_n (hsat : Satisfied2 hash bilateralAggDescriptor minit mfin maddrs t)
    (hpos : 0 < t.rows.length) : nActiveAt t (t.rows.length - 1) = t.pub OuterPi.N_CELLS := by
  have h := piLast_forces hsat hpos mem_lastNEqPi
  simpa only [nActiveAt, rowAt] using h

/-! ## §5 — THE WHOLE-DESCRIPTOR BRIDGE (SAT_IMPLIES_SEM). -/

/-- **`bilateralAgg_refines` — the Rung-1 functional-correctness refinement.**

A non-empty trace that SATISFIES the emitted `bilateralAggDescriptor` (via the deployed acceptance
predicate `Satisfied2`) IS a genuine bilateral-bundle aggregation `BundleAggregated t`: the bundle's
first and last cell carry the published turn identity, every non-final cell replays its schedule,
there is EXACTLY ONE agent cell across the bundle, and the published `n_cells` counts the consistent
cells. The two cumulative facts are threaded from the row-0 seeds to the last-row boundaries by
`running_sum` — the genuine aggregation content, not a per-gate restatement. No crypto carrier is
consumed. -/
theorem bilateralAgg_refines
    (hsat : Satisfied2 hash bilateralAggDescriptor minit mfin maddrs t) (hne : t.rows ≠ []) :
    BundleAggregated t := by
  have hpos : 0 < t.rows.length := List.length_pos_of_ne_nil hne
  refine
    { nonempty := hpos
      turnHashFirst := fun i hi => ?_
      effectsFirst := fun i hi => ?_
      actorNonceFirst := ?_
      prevReceiptFirst := fun i hi => ?_
      turnHashLast := fun i hi => ?_
      effectsLast := fun i hi => ?_
      actorNonceLast := ?_
      prevReceiptLast := fun i hi => ?_
      replayCounts := fun i hii k hk => ?_
      replayRoots := fun i hii k hk => ?_
      exactlyOneAgent := ?_
      publishedCount := ?_ }
  · simpa only [rowAt] using piFirst_forces hsat hpos (mem_A (mem_turn_hash .first i hi))
  · simpa only [rowAt] using piFirst_forces hsat hpos (mem_A (mem_turn_effects .first i hi))
  · simpa only [rowAt] using piFirst_forces hsat hpos (mem_A (mem_turn_nonce .first))
  · simpa only [rowAt] using piFirst_forces hsat hpos (mem_A (mem_turn_prev .first i hi))
  · simpa only [rowAt] using piLast_forces hsat hpos (mem_B (mem_turn_hash .last i hi))
  · simpa only [rowAt] using piLast_forces hsat hpos (mem_B (mem_turn_effects .last i hi))
  · simpa only [rowAt] using piLast_forces hsat hpos (mem_B (mem_turn_nonce .last))
  · simpa only [rowAt] using piLast_forces hsat hpos (mem_B (mem_turn_prev .last i hi))
  · -- replayCounts on a non-final cell
    have hi : i < t.rows.length := by omega
    have hnl : i + 1 ≠ t.rows.length := by omega
    have h := gate_forces hsat hi hnl (mem_scheduleReplay_counts k hk)
    simp only [cg3Eq, colEqCol, EmittedExpr.eval, rowAt] at h ⊢
    omega
  · -- replayRoots on a non-final cell
    have hi : i < t.rows.length := by omega
    have hnl : i + 1 ≠ t.rows.length := by omega
    have h := gate_forces hsat hi hnl (mem_scheduleReplay_roots k hk)
    simp only [cg3Eq, colEqCol, EmittedExpr.eval, rowAt] at h ⊢
    omega
  · -- exactlyOneAgent: cum(last) = prefixSum is_agent, and cum(last) = 1
    have key := running_sum t.rows.length (cumAt t) (isAgentAt t) (seed_cum hsat hpos)
      (fun i hii => step_cum hsat i hii) (t.rows.length - 1) (by omega)
    rw [← key]; exact last_cum hsat hpos
  · -- publishedCount: n(last) = prefixSum consistent, and n(last) = pi[N_CELLS]
    have key := running_sum t.rows.length (nActiveAt t) (consistentAt t) (seed_n hsat hpos)
      (fun i hii => step_n hsat i hii) (t.rows.length - 1) (by omega)
    rw [← key]; exact (last_n hsat hpos).symm

end Extract

/-! ## §6 — Non-vacuity: a concrete satisfying witness AND a concrete failing one. -/

/-- The abstract hash never enters this descriptor's denotation (no hash-sites / map-ops). -/
def hash0 : List ℤ → ℤ := fun _ => 0

theorem memOpsOf_agg : memOpsOf bilateralAggDescriptor = [] := rfl
theorem mapOpsOf_agg : mapOpsOf bilateralAggDescriptor = [] := rfl
theorem memLog_agg (t : VmTrace) : memLog bilateralAggDescriptor t = [] := by
  simp [memLog, memOpsOf_agg]
theorem mapLog_agg (t : VmTrace) : mapLog bilateralAggDescriptor t = [] := by
  simp [mapLog, mapOpsOf_agg]

/-- Cell 0: a NON-agent, consistent cell (`is_agent=0`, `cum=0`, `consistent=1`, `n=1`); turn-id /
counts / roots / expected columns all `0`. -/
def wr0 : Assignment := fun j => if j = 85 then 1 else if j = 86 then 1 else 0
/-- Cell 1 (the last cell): THE agent cell (`is_agent=1`, `cum=1`, `consistent=1`, `n=2`). -/
def wr1 : Assignment :=
  fun j => if j = 48 then 1 else if j = 84 then 1 else if j = 85 then 1 else if j = 86 then 2 else 0
/-- The public inputs: `pi[N_CELLS] = 2` (the two active cells); everything else `0`. -/
def wpub : Assignment := fun j => if j = 21 then 2 else 0
/-- The concrete 2-cell bundle: cell 0 (non-agent, consistent) · cell 1 (the agent cell). -/
def witTrace : VmTrace := { rows := [wr0, wr1], pub := wpub, tf := fun _ => [] }

/-- **The witness PROVABLY satisfies the emitted descriptor.** Every row constraint holds on both
cells (the CG-2 pins by value agreement; CG-3 replay by `0 = 0` on cell 0, vacuous on the last cell;
CG-4 booleans / padding / the two cumulative windows; the boundaries), and the memory legs are the
empty-log balance. -/
theorem witTrace_satisfies :
    Satisfied2 hash0 bilateralAggDescriptor (fun _ => 0) (fun _ => (0, 0)) [] witTrace where
  rowConstraints := by
    intro i hi c hc
    have hi2 : i < 2 := hi
    rw [show witTrace.rows.length = 2 from rfl]
    simp only [bilateralAggDescriptor] at hc
    interval_cases i <;>
      fin_cases hc <;>
      simp only [cg2PiBind, cg3Eq, colEqCol, boolGate, paddingGate, cumAgentTransition,
        cumActiveTransition, firstCumSeed, firstNSeed, lastCumIsOne, lastNEqPi,
        VmConstraint2.holdsAt, VmConstraint.holdsVm, WindowConstraint.holdsAt,
        witTrace, envAt, wr0, wr1, wpub, EmittedExpr.eval, WindowExpr.eval,
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

/-- **The bridge FIRES on the witness** (the SAT hypothesis is genuinely inhabited): the concrete
2-cell bundle is a `BundleAggregated`. -/
theorem witness_aggregated : BundleAggregated witTrace :=
  bilateralAgg_refines witTrace_satisfies (by decide)

/-- The recovered aggregation is CONCRETE and non-trivial: exactly ONE agent cell
(`is_agent 0 + is_agent 1 = 0 + 1 = 1`), and the published count is `2` = the two consistent cells
(`1 + 1`). The two cumulative recurrences and the schedule replay on cell 0 were all exercised. -/
theorem witness_value :
    prefixSum (isAgentAt witTrace) (witTrace.rows.length - 1) = 1 ∧
    witTrace.pub OuterPi.N_CELLS = 2 ∧
    prefixSum (consistentAt witTrace) (witTrace.rows.length - 1) = 2 := by
  refine ⟨witness_aggregated.exactlyOneAgent, by decide, ?_⟩
  have := witness_aggregated.publishedCount
  simpa using this.symm

/-- A WRONG bundle: a single cell whose `is_agent_cumulative` is `0`, not the required `1`. -/
def badTrace : VmTrace := { rows := [zeroAsg], pub := zeroAsg, tf := fun _ => [] }

/-- **A WRONG bundle PROVABLY fails the hypothesis** (the constraint bites — the Satisfied2 accept-set
does NOT contain this trace): the single-agent boundary `lastCumIsOne` forces the last-row cumulative
to `1`, but `badTrace` carries `0`, so no `Satisfied2` witness exists. -/
theorem badTrace_not_satisfied :
    ¬ Satisfied2 hash0 bilateralAggDescriptor (fun _ => 0) (fun _ => (0, 0)) [] badTrace := by
  intro h
  exact absurd (last_cum h (by decide)) (by decide)

/-! ## §7 — Axiom tripwires. -/

#assert_axioms bilateralAgg_refines
#assert_axioms witTrace_satisfies
#assert_axioms witness_aggregated
#assert_axioms witness_value
#assert_axioms badTrace_not_satisfied

end Dregg2.Circuit.Emit.BilateralAggregationRefine

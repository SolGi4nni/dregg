/-
# Dregg2.Circuit.Emit.BridgeActionRefine — the WHOLE-DESCRIPTOR functional-correctness bridge for
the bridge-action binding leaf (`BridgeActionEmit.bridgeActionDesc`).

## What Rung-0 already proved (in `BridgeActionEmit.lean`)
`bridgeActionDesc` is byte-pinned to the hand AIR, and each gate has a LOCAL soundness lemma
(`cont_body_zero_iff`: the per-column continuity poly vanishes iff that column chains).

## What THIS file proves (Rung-1)
The census dossier for `bridge_action` is `spec_status = NO_LEAN`: no proven semantic model existed.
So this file FIRST authors the missing functional spec — the genuine relation the binding AIR is
meant to compute — then proves the emitted descriptor refines it, whole-descriptor, IN BOTH
DIRECTIONS.

### The semantic relation (authored here)
`bridge_action_air` is a BINDING-ONLY AIR: it publishes a 26-limb typed tuple
(8-limb `nullifier` ‖ 8-limb `recipient` ‖ 8-limb `destination_federation` ‖ `amount_lo` ‖
`amount_hi`) in the 26 public inputs and forces EVERY trace row (row 0 by the boundary pins, every
padding row by the transition continuity) to carry EXACTLY that tuple. The functional spec is
therefore:

  * `BridgeAction` — the typed tuple the circuit computes over.
  * `BridgeAction.decodeAt` — decode the identity-layout 8/8/8/2 columns of an assignment into it.
  * `BridgeRowBinds row pub` — every one of the 26 typed columns of `row` equals the published input.
  * `BridgeActionBinds t` — the WHOLE-TRACE relation: every row of the trace binds the published
    26-limb tuple.

### The bridge (whole descriptor, not one gate)
`bridgeAction_satisfied2_binds` (SAT ⟹ SEM, the load-bearing soundness direction): a trace that
SATISFIES the whole descriptor (`Satisfied2`) binds the published tuple in every row. This is NOT a
single-gate restatement — it COMPOSES all 26 boundary pins (giving row 0) with all 26 transition
gates (propagating row 0 to every padding row by induction over the trace). `carriesTuple_decode`
lifts this to the typed conclusion `decodeAt (row i) = decodeAt pub` for every row `i`.
`bridgeAction_binds_satisfied2` (SEM ⟹ SAT) completes the equivalence over binding traces (no
memory/map-ops tables), so `bridgeAction_satisfied2_iff` is the full IFF.

### Non-vacuity (the anti-scar proof)
`demoTrace_satisfied2` constructs a CONCRETE satisfying witness (a 26-limb tuple, distinct per
column, carried across two rows) — the hypothesis is genuinely inhabited, and the bridge fires
end-to-end on it (`demoTrace_decode0`). `brokenBound_rejects` and `brokenPad_rejects` exhibit two
CONCRETE traces each of which FAILS `Satisfied2` because a constraint BITES: a forged row-0 limb
trips a boundary pin, and a mismatched padding row trips a transition gate.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. NO cryptographic carrier: the binding AIR
has no hash sites / ranges / map ops, so no Poseidon2 CR enters. NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.BridgeActionEmit

namespace Dregg2.Circuit.Emit.BridgeActionRefine

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 WindowConstraint WindowExpr Satisfied2 VmTrace TraceFamily
   TableId envAt zeroAsg memOpsOf mapOpsOf memLog mapLog opRow memCheck_nil)
open Dregg2.Circuit.Emit.BridgeActionEmit
  (bridgeActionDesc contBody cont_body_zero_iff piPins windowGates BRIDGE_ACTION_WIDTH)

set_option autoImplicit false

/-! ## §1 — The authored functional spec: the typed bridge-action tuple + the binding relation. -/

/-- The typed bridge-action tuple the binding AIR computes over: the 8/8/8/2 identity layout of
`bridge_action_air.rs` (nullifier ‖ recipient ‖ destination_federation ‖ amount_lo ‖ amount_hi). -/
structure BridgeAction where
  nullifier      : Fin 8 → ℤ
  recipient      : Fin 8 → ℤ
  destFederation : Fin 8 → ℤ
  amountLo       : ℤ
  amountHi       : ℤ

/-- Decode an assignment's identity-layout columns `0..25` into the typed tuple (the same decode the
public inputs and every trace row are read through — `pi_index == col`). -/
def BridgeAction.decodeAt (a : Assignment) : BridgeAction :=
  { nullifier      := fun j => a j.val
  , recipient      := fun j => a (8 + j.val)
  , destFederation := fun j => a (16 + j.val)
  , amountLo       := a 24
  , amountHi       := a 25 }

/-- A row BINDS the published tuple: every one of the 26 typed columns equals the published input.
The identity-layout face of "this row carries exactly the bridge-action tuple in the PIs". -/
def BridgeRowBinds (row pub : Assignment) : Prop :=
  ∀ c, c < BRIDGE_ACTION_WIDTH → row c = pub c

/-- **`BridgeActionBinds t`** — THE whole-trace semantic relation the binding AIR computes: every row
of the trace binds the published 26-limb bridge-action tuple. -/
def BridgeActionBinds (t : VmTrace) : Prop :=
  ∀ i, i < t.rows.length → BridgeRowBinds (t.rows.getD i zeroAsg) t.pub

/-- The typed face of `BridgeRowBinds`: a binding row DECODES to the same `BridgeAction` as the
published inputs — the functional-correctness statement made explicit over the typed tuple. -/
theorem carriesTuple_decode (row pub : Assignment) (h : BridgeRowBinds row pub) :
    BridgeAction.decodeAt row = BridgeAction.decodeAt pub := by
  simp only [BridgeRowBinds, BRIDGE_ACTION_WIDTH] at h
  simp only [BridgeAction.decodeAt, BridgeAction.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · funext j; exact h j.val (by have := j.isLt; omega)
  · funext j; exact h (8 + j.val) (by have := j.isLt; omega)
  · funext j; exact h (16 + j.val) (by have := j.isLt; omega)
  · exact h 24 (by omega)
  · exact h 25 (by omega)

/-! ## §2 — The per-constraint reductions (the STABLE surface to the two gate families). -/

/-- A boundary pin's per-row denotation IS its first-row PI equality (`pi_index == col`). -/
theorem base_piPin_holdsAt (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (isFirst isLast : Bool) (c : Nat) :
    (VmConstraint2.base (VmConstraint.piBinding VmRow.first c c)).holdsAt hash tf env isFirst isLast
      ↔ (isFirst = true → env.loc c = env.pub c) := Iff.rfl

/-- A continuity gate's per-row denotation IS "off the last row, this column chains" — via the
Rung-0 tooth `cont_body_zero_iff`. -/
theorem windowGate_holdsAt (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (isFirst isLast : Bool) (c : Nat) :
    (VmConstraint2.windowGate ⟨contBody c, true⟩).holdsAt hash tf env isFirst isLast
      ↔ (isLast = false → env.nxt c = env.loc c) := by
  constructor
  · intro h hl; exact (cont_body_zero_iff env c).mp (h hl)
  · intro h hl; exact (cont_body_zero_iff env c).mpr (h hl)

/-! ## §3 — The two constraint families' membership in the descriptor. -/

/-- The boundary pin at column `c` is a declared constraint (`c < 26`). -/
theorem piPin_mem (c : Nat) (hc : c < BRIDGE_ACTION_WIDTH) :
    (VmConstraint2.base (VmConstraint.piBinding VmRow.first c c)) ∈ bridgeActionDesc.constraints := by
  show _ ∈ piPins ++ windowGates
  exact List.mem_append_left _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩)

/-- The continuity gate at column `c` is a declared constraint (`c < 26`). -/
theorem windowGate_mem (c : Nat) (hc : c < BRIDGE_ACTION_WIDTH) :
    (VmConstraint2.windowGate ⟨contBody c, true⟩) ∈ bridgeActionDesc.constraints := by
  show _ ∈ piPins ++ windowGates
  exact List.mem_append_right _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩)

/-! ## §4 — THE BRIDGE (SAT ⟹ SEM): a satisfying trace binds the published tuple in every row. -/

/-- **`bridgeAction_satisfied2_binds` — THE whole-descriptor soundness bridge.** A trace that
satisfies the whole `bridgeActionDesc` (`Satisfied2`) binds the published 26-limb bridge-action
tuple in EVERY row. Composes the 26 boundary pins (row 0) with the 26 transition gates (propagated
to every padding row by induction) — this is the whole descriptor, not one gate. -/
theorem bridgeAction_satisfied2_binds
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (h : Satisfied2 hash bridgeActionDesc minit mfin maddrs t) :
    BridgeActionBinds t := by
  -- boundary: row 0 binds the published tuple.
  have row0 : 0 < t.rows.length → BridgeRowBinds (t.rows.getD 0 zeroAsg) t.pub := by
    intro hpos c hc
    have hpin := h.rowConstraints 0 hpos _ (piPin_mem c hc)
    rw [base_piPin_holdsAt] at hpin
    simpa [envAt] using hpin rfl
  -- continuity: consecutive active rows agree on every typed column.
  have step : ∀ i, i + 1 < t.rows.length →
      BridgeRowBinds (t.rows.getD (i + 1) zeroAsg) (t.rows.getD i zeroAsg) := by
    intro i hi1 c hc
    have hgate := h.rowConstraints i (by omega) _ (windowGate_mem c hc)
    rw [windowGate_holdsAt] at hgate
    have hlast : (i + 1 == t.rows.length) = false := by rw [beq_eq_false_iff_ne]; omega
    simpa [envAt] using hgate hlast
  -- induction: row 0 (boundary) propagated to every row (continuity).
  intro i
  induction i with
  | zero => intro hi; exact row0 hi
  | succ k ih =>
    intro hi c hc
    have hk := ih (by omega) c hc
    have hs := step k hi c hc
    rw [hs, hk]

/-- **The typed corollary:** every row of a satisfying trace DECODES to the same `BridgeAction` as
the public inputs — functional correctness of the binding AIR, over the typed tuple. -/
theorem bridgeAction_satisfied2_decodes
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (h : Satisfied2 hash bridgeActionDesc minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    BridgeAction.decodeAt (t.rows.getD i zeroAsg) = BridgeAction.decodeAt t.pub :=
  carriesTuple_decode _ _ (bridgeAction_satisfied2_binds hash minit mfin maddrs t h i hi)

/-! ## §5 — Completeness (SEM ⟹ SAT) over binding traces, and the full IFF. -/

/-- The binding descriptor declares no memory ops. -/
theorem bridge_memOps : memOpsOf bridgeActionDesc = [] := rfl
/-- The binding descriptor declares no map ops. -/
theorem bridge_mapOps : mapOpsOf bridgeActionDesc = [] := rfl

/-- Hence its gathered memory log is empty on any trace. -/
theorem bridge_memLog (t : VmTrace) : memLog bridgeActionDesc t = [] := by
  simp only [memLog, bridge_memOps, List.filterMap_nil]
  induction t.rows with
  | nil => simp
  | cons a as ih => simp [ih]

/-- Hence its gathered map-ops log is empty on any trace. -/
theorem bridge_mapLog (t : VmTrace) : mapLog bridgeActionDesc t = [] := by
  simp only [mapLog, bridge_mapOps, List.filterMap_nil]
  induction t.rows with
  | nil => simp
  | cons a as ih => simp [ih]

/-- **`bridgeAction_binds_satisfied2` — completeness.** A binding trace (no memory/map-ops tables)
that binds the published tuple in every row SATISFIES the whole descriptor. -/
theorem bridgeAction_binds_satisfied2 (t : VmTrace)
    (hmem : t.tf TableId.memory = []) (hmap : t.tf TableId.mapOps = [])
    (hbind : BridgeActionBinds t) :
    Satisfied2 (fun _ => 0) bridgeActionDesc (fun _ => 0) (fun _ => (0, 0)) [] t := by
  refine ⟨?_, ?_, ?_, List.nodup_nil, ?_, ?_, ?_, ?_, ?_⟩
  · -- rowConstraints
    intro i hi c hc
    rw [show bridgeActionDesc.constraints = piPins ++ windowGates from rfl] at hc
    rcases List.mem_append.mp hc with hp | hw
    · obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hp
      rw [base_piPin_holdsAt]
      intro hfirst
      have hcw : c' < BRIDGE_ACTION_WIDTH := List.mem_range.mp hc'
      have hi0 : i = 0 := by simpa using hfirst
      subst hi0
      simpa [envAt] using hbind 0 hi c' hcw
    · obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hw
      rw [windowGate_holdsAt]
      intro hlast
      have hcw : c' < BRIDGE_ACTION_WIDTH := List.mem_range.mp hc'
      have hi1 : i + 1 < t.rows.length := by
        have := beq_eq_false_iff_ne.mp hlast; omega
      have hk := hbind i (by omega) c' hcw
      have hk1 := hbind (i + 1) hi1 c' hcw
      simp only [envAt]
      rw [hk1, hk]
  · -- rowHashes: no hash sites
    intro i hi; trivial
  · -- rowRanges: no ranges
    intro i hi r hr; simp [bridgeActionDesc] at hr
  · -- memClosed: empty memory log
    intro op hop; simp [bridge_memLog] at hop
  · -- memDisciplined
    rw [bridge_memLog t]; exact (by decide)
  · -- memBalanced
    rw [bridge_memLog t]; exact memCheck_nil _ _
  · -- memTableFaithful
    simp [hmem, bridge_memLog]
  · -- mapTableFaithful
    simp [hmap, bridge_mapLog]

/-- **`bridgeAction_satisfied2_iff` — THE full equivalence.** Over a binding trace (no memory/map-ops
tables), the whole descriptor's accept-set is EXACTLY the traces that bind the published bridge-action
tuple in every row. -/
theorem bridgeAction_satisfied2_iff (t : VmTrace)
    (hmem : t.tf TableId.memory = []) (hmap : t.tf TableId.mapOps = []) :
    Satisfied2 (fun _ => 0) bridgeActionDesc (fun _ => 0) (fun _ => (0, 0)) [] t
      ↔ BridgeActionBinds t := by
  constructor
  · exact bridgeAction_satisfied2_binds _ _ _ _ t
  · exact bridgeAction_binds_satisfied2 t hmem hmap

/-! ## §6 — Non-vacuity: a CONCRETE satisfying witness (bridge fires) + two failing ones (gate bites). -/

/-- A concrete published tuple: column `c` holds the distinct value `c` (a real 26-limb tuple). -/
def demoPub : Assignment := fun c => (c : ℤ)

/-- A concrete satisfying binding trace: two rows, each carrying `demoPub`, published as the PIs. -/
def demoTrace : VmTrace := { rows := [demoPub, demoPub], pub := demoPub, tf := fun _ => [] }

/-- The demo trace binds the published tuple in every row. -/
theorem demoTrace_binds : BridgeActionBinds demoTrace := by
  intro i hi c _
  have hi2 : i < 2 := hi
  interval_cases i <;> rfl

/-- **Non-vacuity (accept) — the hypothesis is GENUINELY inhabited.** The demo trace SATISFIES the
whole descriptor (built through the completeness direction). -/
theorem demoTrace_satisfied2 :
    Satisfied2 (fun _ => 0) bridgeActionDesc (fun _ => 0) (fun _ => (0, 0)) [] demoTrace :=
  bridgeAction_binds_satisfied2 demoTrace rfl rfl demoTrace_binds

/-- **The bridge fires end-to-end on the concrete witness** (SAT ⟹ SEM, non-vacuously). -/
theorem demoTrace_binds_via_bridge : BridgeActionBinds demoTrace :=
  bridgeAction_satisfied2_binds _ _ _ _ demoTrace demoTrace_satisfied2

/-- The typed conclusion, concretely: row 0 of the satisfying trace decodes to the published tuple. -/
theorem demoTrace_decode0 :
    BridgeAction.decodeAt (demoTrace.rows.getD 0 zeroAsg) = BridgeAction.decodeAt demoTrace.pub :=
  bridgeAction_satisfied2_decodes _ _ _ _ demoTrace demoTrace_satisfied2 0 (by decide)

/-- A forged row-0 whose limb 0 (`999`) does NOT match the published input (`0`). -/
def brokenBoundRow : Assignment := fun c => if c = 0 then 999 else (c : ℤ)
/-- A trace whose only row carries the forged limb — the boundary PI layout is violated. -/
def brokenBoundTrace : VmTrace := { rows := [brokenBoundRow], pub := demoPub, tf := fun _ => [] }

/-- **Non-vacuity (reject — boundary tooth BITES).** The forged-limb trace FAILS `Satisfied2`: the
column-0 boundary pin forces `row0[0] = pub[0]`, i.e. `999 = 0`. -/
theorem brokenBound_rejects :
    ¬ Satisfied2 (fun _ => 0) bridgeActionDesc (fun _ => 0) (fun _ => (0, 0)) [] brokenBoundTrace := by
  intro h
  have hpin := h.rowConstraints 0 (by decide) _ (piPin_mem 0 (by decide))
  rw [base_piPin_holdsAt] at hpin
  have hbad := hpin rfl
  simp [envAt, brokenBoundTrace, brokenBoundRow, demoPub] at hbad

/-- A trace whose padding row (row 1) carries a DIFFERENT limb 0 (`999`) than row 0 (`0`). -/
def brokenPadRow : Assignment := fun c => if c = 0 then 999 else (c : ℤ)
/-- Row 0 matches the PIs, but the padding row breaks continuity at column 0. -/
def brokenPadTrace : VmTrace := { rows := [demoPub, brokenPadRow], pub := demoPub, tf := fun _ => [] }

/-- **Non-vacuity (reject — continuity tooth BITES).** The mismatched-padding trace FAILS
`Satisfied2`: the column-0 transition gate on row 0 forces `row1[0] = row0[0]`, i.e. `999 = 0` — this
is exactly the "prover binds a different tuple in a padding row" attack the descriptor forbids. -/
theorem brokenPad_rejects :
    ¬ Satisfied2 (fun _ => 0) bridgeActionDesc (fun _ => 0) (fun _ => (0, 0)) [] brokenPadTrace := by
  intro h
  have hgate := h.rowConstraints 0 (by decide) _ (windowGate_mem 0 (by decide))
  rw [windowGate_holdsAt] at hgate
  have hbad := hgate (by decide)
  simp [envAt, brokenPadTrace, brokenPadRow, demoPub] at hbad

/-! ### Shape pins. -/

#guard decide (demoTrace.rows.length = 2)
#guard decide (brokenBoundTrace.rows.length = 1)
#guard decide (brokenPadTrace.rows.length = 2)

#assert_axioms carriesTuple_decode
#assert_axioms bridgeAction_satisfied2_binds
#assert_axioms bridgeAction_satisfied2_decodes
#assert_axioms bridgeAction_binds_satisfied2
#assert_axioms bridgeAction_satisfied2_iff
#assert_axioms demoTrace_satisfied2
#assert_axioms brokenBound_rejects
#assert_axioms brokenPad_rejects

end Dregg2.Circuit.Emit.BridgeActionRefine

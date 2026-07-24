/-
# Dregg2.Circuit.Emit.MerkleMembership4aryRefine

Whole-descriptor soundness for the deployed depth-general 4-ary membership
artifact.  Satisfaction of the emitted IR2 constraints implies the genuine
positional Poseidon fold from public leaf to public root.
-/
import Dregg2.Circuit.Emit.MerkleMembership4aryEmit
import Dregg2.Circuit.Emit.BlindedMembershipRefine
import Dregg2.Circuit.DecideSatisfied2

namespace Dregg2.Circuit.Emit.MerkleMembership4aryRefine

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (Satisfied2 VmTrace envAt VmConstraint2 Lookup TableId ChipTableSound chip_lookup_sound
   chipLookupTuple chipLookupTupleNarrow poseidon2narrow CHIP_RATE memLog mapLog memCheck_nil
   WindowConstraint WindowExpr)
open Dregg2.Circuit.Emit.BlindedMembershipEmit
  (gPerRowBodies gPerRowGates gLastRowBoundaries gParentLookupNarrow gContinuity gContWindow
   gCUR gSIB0 gSIB1 gSIB2 gB0 gB1 gC0 gC1 gC2 gC3 gPAR gPATH_LANES
   gArrangeList bitBinaryBody child0Body child1Body child2Body child3Body)
open Dregg2.Circuit.Emit.BlindedMembershipRefine
  (gStep gFoldPos gFoldPos_concat gStepsOf GRowCanon gChildren_arranged_canon)
open Dregg2.Circuit.Emit.MerkleMembership4aryEmit
  (membership4aryDesc membership4aryConstraints leafPin rootPin PI_LEAF PI_ROOT)
open Dregg2.Circuit.Emit.MerkleMembershipRefine (Canon eq_of_modEq_canon)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff pPrimeInt)

set_option autoImplicit false

/-- Trace-independent statement forced by the emitted descriptor. -/
def Membership4ary (hash : List ℤ → ℤ) (leaf root : ℤ)
    (steps : List (ℤ × ℤ × ℤ × ℤ × ℤ)) : Prop :=
  gFoldPos hash leaf steps = root

/-- Canonical field representatives needed to lift field equalities through
the abstract hash boundary. -/
structure MembershipCanon (t : VmTrace) : Prop where
  rows : ∀ j, j < t.rows.length → GRowCanon (envAt t j).loc
  leaf : Canon (t.pub PI_LEAF)
  root : Canon (t.pub PI_ROOT)

variable {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ}
  {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}

/-- Every position/arrangement body holds on every row, including the last
row through the explicit boundary repairs. -/
theorem perRowBodyZero
    (hsat : Satisfied2 hash membership4aryDesc minit mfin maddrs t)
    (b : EmittedExpr) (hb : b ∈ gPerRowBodies) (j : Nat) (hj : j < t.rows.length) :
    b.eval (envAt t j).loc ≡ 0 [ZMOD 2013265921] := by
  by_cases hlast : (j + 1 == t.rows.length) = true
  · have hmem : VmConstraint2.base (.boundary VmRow.last b)
        ∈ membership4aryDesc.constraints := by
      show _ ∈ membership4aryConstraints
      simp only [membership4aryConstraints, gLastRowBoundaries, List.mem_append, List.mem_map]
      exact Or.inr ⟨b, hb, rfl⟩
    have h := hsat.rowConstraints j hj _ hmem
    simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm] at h
    exact h hlast
  · have hf : (j + 1 == t.rows.length) = false := by
      simpa only [Bool.not_eq_true] using hlast
    have hmem : VmConstraint2.base (.gate b) ∈ membership4aryDesc.constraints := by
      show _ ∈ membership4aryConstraints
      simp only [membership4aryConstraints, gPerRowGates, List.mem_append, List.mem_map]
      exact Or.inl (Or.inl ⟨b, hb, rfl⟩)
    have h := hsat.rowConstraints j hj _ hmem
    simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hf] at h
    exact h

/-- The six row gates force the genuine positional child arrangement. -/
theorem arrangeAt (hsat : Satisfied2 hash membership4aryDesc minit mfin maddrs t)
    (hcanon : MembershipCanon t) (j : Nat) (hj : j < t.rows.length) :
    [(envAt t j).loc gC0, (envAt t j).loc gC1, (envAt t j).loc gC2,
      (envAt t j).loc gC3]
      = gArrangeList ((envAt t j).loc gCUR) ((envAt t j).loc gSIB0)
          ((envAt t j).loc gSIB1) ((envAt t j).loc gSIB2)
          ((envAt t j).loc gB0) ((envAt t j).loc gB1) := by
  have hz := fun b hb => perRowBodyZero hsat b hb j hj
  exact gChildren_arranged_canon
    (hz _ (by simp [gPerRowBodies])) (hz _ (by simp [gPerRowBodies]))
    (hz _ (by simp [gPerRowBodies])) (hz _ (by simp [gPerRowBodies]))
    (hz _ (by simp [gPerRowBodies])) (hz _ (by simp [gPerRowBodies]))
    (hcanon.rows j hj)

/-- The emitted Poseidon2 lookup binds the parent digest on every row. -/
theorem parentAt (hsat : Satisfied2 hash membership4aryDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (hwire : t.tf poseidon2narrow
      = Dregg2.Circuit.ChipNarrowLookup.narrowTable (t.tf .poseidon2))
    (j : Nat) (hj : j < t.rows.length) :
    (envAt t j).loc gPAR =
      hash [(envAt t j).loc gC0, (envAt t j).loc gC1,
        (envAt t j).loc gC2, (envAt t j).loc gC3] := by
  have hmem : gParentLookupNarrow ∈ membership4aryDesc.constraints := by
    simp [membership4aryDesc, membership4aryConstraints]
  have h := hsat.rowConstraints j hj _ hmem
  simp only [gParentLookupNarrow, VmConstraint2.holdsAt, Lookup.holdsAt] at h
  rw [hwire] at h
  have hs := Dregg2.Circuit.ChipNarrowLookup.chip_lookup_narrow_sound_of_wide_table hash
    (t.tf .poseidon2) hChip (envAt t j).loc
    [.var gC0, .var gC1, .var gC2, .var gC3] gPAR
    (by show (4 : Nat) ≤ CHIP_RATE; decide) h
  simpa [EmittedExpr.eval] using hs

/-- The window gate chains each parent into the next row's running value. -/
theorem continuityAt (hsat : Satisfied2 hash membership4aryDesc minit mfin maddrs t)
    (hcanon : MembershipCanon t) (j : Nat) (hj : j < t.rows.length)
    (hnl : (j + 1 == t.rows.length) = false) :
    (envAt t (j + 1)).loc gCUR = (envAt t j).loc gPAR := by
  have hmem : gContinuity ∈ membership4aryDesc.constraints := by
    simp [membership4aryDesc, membership4aryConstraints]
  have h := hsat.rowConstraints j hj _ hmem
  simp only [gContinuity, VmConstraint2.holdsAt, WindowConstraint.holdsAt, if_true] at h
  have hz : gContWindow.eval (envAt t j) ≡ 0 [ZMOD 2013265921] := h hnl
  have hkey : (envAt t j).nxt gCUR ≡ (envAt t j).loc gPAR [ZMOD 2013265921] :=
    (gate_modEq_iff (by simp only [gContWindow, WindowExpr.eval]; ring)).mp hz
  have hj1 : j + 1 < t.rows.length := by
    simp only [beq_eq_false_iff_ne] at hnl
    omega
  have heq : (envAt t (j + 1)).loc gCUR = (envAt t j).nxt gCUR := rfl
  have hcn : Canon ((envAt t j).nxt gCUR) := heq ▸ (hcanon.rows (j + 1) hj1).cur
  rw [heq]
  exact eq_of_modEq_canon hcn (hcanon.rows j hj).par hkey

theorem leafPi (hsat : Satisfied2 hash membership4aryDesc minit mfin maddrs t)
    (hlen : 0 < t.rows.length) :
    (envAt t 0).loc gCUR ≡ t.pub PI_LEAF [ZMOD 2013265921] := by
  have hmem : leafPin ∈ membership4aryDesc.constraints := by
    simp [membership4aryDesc, membership4aryConstraints]
  have h := hsat.rowConstraints 0 hlen _ hmem
  simp only [leafPin, VmConstraint2.holdsAt, VmConstraint.holdsVm] at h
  exact h (by decide)

theorem rootPi (hsat : Satisfied2 hash membership4aryDesc minit mfin maddrs t)
    (hlen : 0 < t.rows.length) :
    (envAt t (t.rows.length - 1)).loc gPAR ≡ t.pub PI_ROOT [ZMOD 2013265921] := by
  have hmem : rootPin ∈ membership4aryDesc.constraints := by
    simp [membership4aryDesc, membership4aryConstraints]
  have hj : t.rows.length - 1 < t.rows.length := by omega
  have h := hsat.rowConstraints (t.rows.length - 1) hj _ hmem
  simp only [rootPin, VmConstraint2.holdsAt, VmConstraint.holdsVm] at h
  refine h ?_
  have : t.rows.length - 1 + 1 = t.rows.length := by omega
  simp [this]

/-- Cross-row induction: the public-leaf row value folds through every emitted
level to each row's parent. -/
theorem foldsTo (hsat : Satisfied2 hash membership4aryDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (hwire : t.tf poseidon2narrow
      = Dregg2.Circuit.ChipNarrowLookup.narrowTable (t.tf .poseidon2))
    (hcanon : MembershipCanon t) :
    ∀ j, j < t.rows.length →
      gFoldPos hash ((envAt t 0).loc gCUR) (gStepsOf t (j + 1)) =
        (envAt t j).loc gPAR := by
  intro j
  induction j with
  | zero =>
    intro hj0
    have key : gFoldPos hash ((envAt t 0).loc gCUR) (gStepsOf t 1) =
        hash (gArrangeList ((envAt t 0).loc gCUR) ((envAt t 0).loc gSIB0)
          ((envAt t 0).loc gSIB1) ((envAt t 0).loc gSIB2)
          ((envAt t 0).loc gB0) ((envAt t 0).loc gB1)) := by
      simp only [gStepsOf, List.range_one, List.map_cons, List.map_nil, gFoldPos,
        List.foldl_cons, List.foldl_nil, gStep]
    rw [key, ← arrangeAt hsat hcanon 0 hj0, ← parentAt hsat hChip hwire 0 hj0]
  | succ j ih =>
    intro hj
    have hjS : j < t.rows.length := by omega
    have hnl : (j + 1 == t.rows.length) = false := by
      simp only [beq_eq_false_iff_ne]; omega
    have hcont := continuityAt hsat hcanon j hjS hnl
    have hsteps : gStepsOf t (j + 2) = gStepsOf t (j + 1) ++
        [((envAt t (j + 1)).loc gSIB0, (envAt t (j + 1)).loc gSIB1,
          (envAt t (j + 1)).loc gSIB2, (envAt t (j + 1)).loc gB0,
          (envAt t (j + 1)).loc gB1)] := by
      simp only [gStepsOf, List.range_succ, List.map_append, List.map_cons, List.map_nil]
    show gFoldPos hash ((envAt t 0).loc gCUR) (gStepsOf t (j + 1 + 1)) =
      (envAt t (j + 1)).loc gPAR
    have key : gFoldPos hash ((envAt t 0).loc gCUR) (gStepsOf t (j + 1 + 1)) =
        hash (gArrangeList ((envAt t j).loc gPAR) ((envAt t (j + 1)).loc gSIB0)
          ((envAt t (j + 1)).loc gSIB1) ((envAt t (j + 1)).loc gSIB2)
          ((envAt t (j + 1)).loc gB0) ((envAt t (j + 1)).loc gB1)) := by
      rw [show j + 1 + 1 = j + 2 from rfl, hsteps, gFoldPos_concat, ih hjS]
      simp only [gStep]
    rw [key, ← hcont, ← arrangeAt hsat hcanon (j + 1) hj,
      ← parentAt hsat hChip hwire (j + 1) hj]

/-- THE WHOLE-DESCRIPTOR BRIDGE: IR2 satisfaction implies genuine membership. -/
theorem membership4ary_sat_refines
    (hlen : 0 < t.rows.length)
    (hsat : Satisfied2 hash membership4aryDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (hwire : t.tf poseidon2narrow
      = Dregg2.Circuit.ChipNarrowLookup.narrowTable (t.tf .poseidon2))
    (hcanon : MembershipCanon t) :
    Membership4ary hash (t.pub PI_LEAF) (t.pub PI_ROOT) (gStepsOf t t.rows.length) := by
  have hleaf : (envAt t 0).loc gCUR = t.pub PI_LEAF :=
    eq_of_modEq_canon (hcanon.rows 0 hlen).cur hcanon.leaf (leafPi hsat hlen)
  have hj : t.rows.length - 1 < t.rows.length := by omega
  have hfold := foldsTo hsat hChip hwire hcanon (t.rows.length - 1) hj
  rw [Nat.sub_add_cancel hlen] at hfold
  unfold Membership4ary
  rw [← hleaf, hfold]
  exact eq_of_modEq_canon (hcanon.rows (t.rows.length - 1) hj).par hcanon.root
    (rootPi hsat hlen)

/-! A concrete two-row, mixed-position witness proves non-vacuity. -/

private def demoHash : List ℤ → ℤ := fun xs => xs.foldl (fun acc x => acc * 10 + x) 0

private def row0 : Assignment := fun c =>
  if c = gCUR then 1 else if c = gSIB0 then 2 else if c = gSIB1 then 3 else if c = gSIB2 then 4
  else if c = gB0 then 1 else if c = gB1 then 0
  else if c = gC0 then 2 else if c = gC1 then 1 else if c = gC2 then 3 else if c = gC3 then 4
  else if c = gPAR then 2134 else 0

private def row1 : Assignment := fun c =>
  if c = gCUR then 2134 else if c = gSIB0 then 5 else if c = gSIB1 then 6 else if c = gSIB2 then 7
  else if c = gB0 then 0 else if c = gB1 then 0
  else if c = gC0 then 2134 else if c = gC1 then 5 else if c = gC2 then 6 else if c = gC3 then 7
  else if c = gPAR then 2134567 else 0

private def pub : Assignment := fun k => if k = PI_LEAF then 1 else if k = PI_ROOT then 2134567 else 0

private def tbl : List (List ℤ) :=
  [Dregg2.Circuit.DescriptorIR2.chipRow demoHash [2, 1, 3, 4] (List.replicate 7 0),
   Dregg2.Circuit.DescriptorIR2.chipRow demoHash [2134, 5, 6, 7] (List.replicate 7 0)]

private def trace : VmTrace :=
  { rows := [row0, row1], pub := pub
    tf := fun tid => match tid with
      | .poseidon2 => tbl
      | .custom 3  => Dregg2.Circuit.ChipNarrowLookup.narrowTable tbl
      | _ => [] }

/-- **The concrete family wires the NARROW bus to the 18-prefix of the wide chip table** — ONE
physical chip serving both buses, exactly the deployed Rust `narrow_hist` serving (definitional). -/
theorem concrete_narrow_wire :
    trace.tf poseidon2narrow
      = Dregg2.Circuit.ChipNarrowLookup.narrowTable (trace.tf .poseidon2) := rfl

theorem concrete_chipSound : ChipTableSound demoHash (trace.tf .poseidon2) := by
  intro r hr
  simp only [trace, tbl, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h
  · exact ⟨[2, 1, 3, 4], List.replicate 7 0, by decide, by decide, h⟩
  · exact ⟨[2134, 5, 6, 7], List.replicate 7 0, by decide, by decide, h⟩

theorem concrete_sat :
    Satisfied2 demoHash membership4aryDesc (fun _ => 0) (fun _ => (0, 0)) [] trace := by
  have hmemlog : memLog membership4aryDesc trace = [] := rfl
  have hmaplog : mapLog membership4aryDesc trace = [] := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    rw [show trace.rows.length = 2 from rfl] at hi
    rw [show membership4aryDesc.constraints = membership4aryConstraints from rfl] at hc
    interval_cases i <;>
      (fin_cases hc <;>
        simp only [VmConstraint2.holdsAt] <;>
        first
          | exact (Dregg2.Circuit.Argus.InterpCore.decideConstraint_iff _ _ _ _).mp (by decide)
          | exact (Dregg2.Circuit.DecideSatisfied2.decideLookup_iff _ _ _).mp (by decide)
          | exact (Dregg2.Circuit.DecideSatisfied2.decideWindow_iff _ _ _).mp (by decide))
  · intro i _; trivial
  · intro i _ r hr; simp [membership4aryDesc] at hr
  · exact List.nodup_nil
  · intro op hop; rw [hmemlog] at hop; simp at hop
  · rw [hmemlog]; trivial
  · rw [hmemlog]; exact memCheck_nil _ _
  · rw [hmemlog]; rfl
  · rw [hmaplog]; rfl

theorem concrete_canon : MembershipCanon trace := by
  refine ⟨?_, by decide, by decide⟩
  intro j hj
  have h2 : j < 2 := hj
  interval_cases j <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide, by decide⟩

theorem witness_spec :
    Membership4ary demoHash (trace.pub PI_LEAF) (trace.pub PI_ROOT)
      (gStepsOf trace trace.rows.length) :=
  membership4ary_sat_refines (by decide) concrete_sat concrete_chipSound concrete_narrow_wire
    concrete_canon

theorem witness_spec_closed :
    Membership4ary demoHash 1 2134567 [(2, 3, 4, 1, 0), (5, 6, 7, 0, 0)] := by
  unfold Membership4ary gFoldPos gStep gArrangeList demoHash
  decide

theorem witness_wrong_root_rejected :
    ¬ Membership4ary demoHash 1 999 [(2, 3, 4, 1, 0), (5, 6, 7, 0, 0)] := by
  unfold Membership4ary gFoldPos gStep gArrangeList demoHash
  decide

#assert_axioms perRowBodyZero
#assert_axioms arrangeAt
#assert_axioms parentAt
#assert_axioms continuityAt
#assert_axioms leafPi
#assert_axioms rootPi
#assert_axioms foldsTo
#assert_axioms membership4ary_sat_refines
#assert_axioms concrete_narrow_wire
#assert_axioms concrete_chipSound
#assert_axioms concrete_sat
#assert_axioms concrete_canon
#assert_axioms witness_spec
#assert_axioms witness_spec_closed
#assert_axioms witness_wrong_root_rejected

end Dregg2.Circuit.Emit.MerkleMembership4aryRefine

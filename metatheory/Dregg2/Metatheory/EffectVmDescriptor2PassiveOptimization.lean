/-
# Passive-optimization PROOFS for the live EffectVmDescriptor2 denotation

The passive-pass CONTRACTS live in exactly one place,
`Dregg2.Circuit.PassiveDescriptorOptimization`: `PassiveOptimization` (both trace
maps plus the public ABI), `SecurityRefinement` (target acceptance implies source
acceptance after expansion), `CompletenessPreservation` (the converse witness
construction), `SatisfiabilityPreservation` (both, hence equisatisfiability), and
the deliberately separate `ExactCarrierTransport` / `WitnessIsomorphism`.  This
module does not restate any of them: it imports them, and supplies the proofs
that instantiate them.

"Passive" is literal here.  Both directions use the same hash interpretation,
initial/final memory images, and declared address boundary.  The public-input
count is unchanged, and trace maps preserve the complete public assignment.

Two concrete instances are proved.  `eraseName` removes diagnostic metadata that
`Satisfied2` never observes.  More substantially, the derived E1 pass deletes
dead trace columns and proves BOTH witness directions over the canonical
projection defined in the contracts module — rows, public assignments,
constraints, hash/range checks, memory/map logs, every auxiliary table, and the
separate `Satisfied2U` universal-memory legs.  This file does not call arbitrary
constraint reordering passive: the order of memory and map constraints
contributes to `memLog` and `mapLog`.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.Emit.RotWideCompactE1
import Dregg2.Circuit.PassiveDescriptorOptimization
import Mathlib.Data.List.GetD

namespace Dregg2.Metatheory.EffectVmDescriptor2PassiveOptimization

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.PassiveDescriptorOptimization

/-- Existential satisfiability of a live descriptor at a fixed external
boundary.  This is the only bookkeeping definition this module adds on top of
the imported contracts; the pass predicates themselves are
`PassiveOptimization`, `SecurityRefinement`, `CompletenessPreservation` and
`SatisfiabilityPreservation` from `Dregg2.Circuit.PassiveDescriptorOptimization`. -/
def Satisfiable (hash : List Int -> Int) (d : EffectVmDescriptor2)
    (minit : Int -> Int) (mfin : Int -> Int × Nat) (maddrs : List Int) : Prop :=
  Exists fun t => Satisfied2 hash d minit mfin maddrs t

/-! ## A first checked concrete pass -/

/-- Erase diagnostic naming metadata.  The live denotation does not inspect the
`name` field. -/
def eraseName (d : EffectVmDescriptor2) : EffectVmDescriptor2 :=
  { d with name := "" }

@[simp] theorem eraseName_piCount (d : EffectVmDescriptor2) :
    (eraseName d).piCount = d.piCount := rfl

/-- Name erasure is definitionally invisible to every leg of `Satisfied2`. -/
theorem eraseName_satisfied_iff (hash : List Int -> Int)
    (d : EffectVmDescriptor2) (minit : Int -> Int)
    (mfin : Int -> Int × Nat) (maddrs : List Int) (t : VmTrace) :
    Satisfied2 hash (eraseName d) minit mfin maddrs t <->
      Satisfied2 hash d minit mfin maddrs t := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, h.memAddrsNodup, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi c hc
      exact h.rowConstraints i hi c (by simpa [eraseName] using hc)
    · intro i hi
      simpa [eraseName] using h.rowHashes i hi
    · intro i hi r hr
      exact h.rowRanges i hi r (by simpa [eraseName] using hr)
    · intro op hop
      exact h.memClosed op (by
        simpa [eraseName, memLog, memOpsOf] using hop)
    · simpa [eraseName, memLog, memOpsOf] using h.memDisciplined
    · simpa [eraseName, memLog, memOpsOf] using h.memBalanced
    · simpa [eraseName, memLog, memOpsOf] using h.memTableFaithful
    · simpa [eraseName, mapLog, mapOpsOf] using h.mapTableFaithful
  · intro h
    refine ⟨?_, ?_, ?_, h.memAddrsNodup, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi c hc
      exact h.rowConstraints i hi c (by simpa [eraseName] using hc)
    · intro i hi
      simpa [eraseName] using h.rowHashes i hi
    · intro i hi r hr
      exact h.rowRanges i hi r (by simpa [eraseName] using hr)
    · intro op hop
      exact h.memClosed op (by
        simpa [eraseName, memLog, memOpsOf] using hop)
    · simpa [eraseName, memLog, memOpsOf] using h.memDisciplined
    · simpa [eraseName, memLog, memOpsOf] using h.memBalanced
    · simpa [eraseName, memLog, memOpsOf] using h.memTableFaithful
    · simpa [eraseName, mapLog, mapOpsOf] using h.mapTableFaithful

/-- A concrete pass over the live descriptor: strip the diagnostic name, leave
witnesses and the public ABI untouched.  Name erasure moves no constraint, so
the ordered public binding slots are literally the same list. -/
def eraseNamePass (d : EffectVmDescriptor2) : PassiveOptimization d (eraseName d) where
  toTarget := id
  toSource := id
  publicABI := { piCount_eq := rfl, bindingSlots_eq := rfl }
  toTarget_pub := by intro t; rfl
  toSource_pub := by intro t; rfl

/-- Both directions are carried, so name erasure is a checked exact pass. -/
theorem eraseNamePreservation (d : EffectVmDescriptor2) :
    SatisfiabilityPreservation (eraseNamePass d) where
  security := by
    intro hash minit mfin maddrs t h
    exact (eraseName_satisfied_iff hash d minit mfin maddrs t).mp h
  completeness := by
    intro hash minit mfin maddrs t h
    exact (eraseName_satisfied_iff hash d minit mfin maddrs t).mpr h

/-- The concrete pass therefore preserves satisfiability exactly, for every
hash interpretation and every memory boundary. -/
theorem eraseName_satisfiable_iff (hash : List Int -> Int)
    (d : EffectVmDescriptor2) (minit : Int -> Int)
    (mfin : Int -> Int × Nat) (maddrs : List Int) :
    Satisfiable hash d minit mfin maddrs <->
      Satisfiable hash (eraseName d) minit mfin maddrs :=
  satisfiable_iff_of_preservation (eraseNamePreservation d) hash minit mfin maddrs

/-! ## E1 dead-column deletion -/

namespace E1

open Dregg2.Circuit.Emit.RotWideCompactE1
open Dregg2.Circuit.Emit.RotWideCompactS2
open Dregg2.Circuit.Emit.EffectVmEmit

/-! `survivorCols`, `projectRow` and `projectTrace` are NOT redefined here: the
canonical source-to-compact projection is the one the contracts module already
installs as `PassiveDescriptorOptimization.E1.pass`'s `toTarget`, and everything
below is proved about that exact definition. -/

open Dregg2.Circuit.PassiveDescriptorOptimization.E1

/-- Among the columns below `c`, the number of survivors is exactly E1's
subtraction-based compact index. -/
theorem survivor_rank (ks : List Nat) (hks : ks.Nodup) (c : Nat) :
    ((List.range c).filter (fun x => !isKilled ks x)).length = dropIdxG ks c := by
  have hkilledPerm : List.Perm
      ((List.range c).filter (isKilled ks)) (ks.filter (fun k => decide (k < c))) := by
    apply (List.perm_ext_iff_of_nodup
      (List.nodup_range.filter _) (hks.filter _)).2
    intro x
    simp [isKilled, and_comm]
  have hkilled : ((List.range c).filter (isKilled ks)).length = killedBelow ks c := by
    unfold killedBelow
    exact hkilledPerm.length_eq
  have hpartition := List.length_eq_length_filter_add (l := List.range c) (isKilled ks)
  simp only [List.length_range] at hpartition
  unfold dropIdxG
  omega

/-- A surviving in-width source column is recovered at its compact index by
the canonical projection row. -/
theorem survivorCols_getD_dropIdx (source : EffectVmDescriptor2) (ks : List Nat)
    (hks : ks.Nodup) (c default : Nat) (hc : c < source.traceWidth)
    (halive : isKilled ks c = false) :
    (survivorCols source ks).getD (dropIdxG ks c) default = c := by
  have hw : source.traceWidth = (c + 1) + (source.traceWidth - (c + 1)) := by omega
  rw [survivorCols, hw, List.range_add, List.range_succ, List.filter_append,
    List.filter_append]
  rw [← survivor_rank ks hks c]
  simp [halive]

/-- Projection and E1's index map agree on every surviving in-width source
column. -/
theorem projectRow_agree (source : EffectVmDescriptor2) (ks : List Nat)
    (hks : ks.Nodup) (a : Dregg2.Circuit.Assignment) (c : Nat)
    (hc : c < source.traceWidth) (halive : isKilled ks c = false) :
    projectRow source ks a (dropIdxG ks c) = a c := by
  unfold projectRow
  rw [survivorCols_getD_dropIdx source ks hks c _ hc halive]

/-- The fallback branch of `projectRow` handles total assignments beyond the
declared source width.  Consequently agreement holds for every non-killed
column, not only descriptor-well-formed in-width references. -/
theorem projectRow_agree_notKilled (source : EffectVmDescriptor2) (ks : List Nat)
    (hks : ks.Nodup) (hwidth : ∀ k ∈ ks, k < source.traceWidth)
    (a : Dregg2.Circuit.Assignment) (c : Nat)
    (halive : isKilled ks c = false) :
    projectRow source ks a (dropIdxG ks c) = a c := by
  by_cases hc : c < source.traceWidth
  · exact projectRow_agree source ks hks a c hc halive
  · have hfilterC : ks.filter (fun k => k < c) = ks := by
      apply List.filter_eq_self.2
      intro k hk
      simpa using Nat.lt_of_lt_of_le (hwidth k hk) (Nat.le_of_not_gt hc)
    have hfilterW : ks.filter (fun k => k < source.traceWidth) = ks := by
      apply List.filter_eq_self.2
      intro k hk
      simpa using hwidth k hk
    have hkbelowC : killedBelow ks c = ks.length := by
      simp [killedBelow, hfilterC]
    have hkbelowW : killedBelow ks source.traceWidth = ks.length := by
      simp [killedBelow, hfilterW]
    have hsub : ks.toFinset ⊆ Finset.range source.traceWidth := by
      intro k hk
      simp only [List.mem_toFinset] at hk
      simpa using hwidth k hk
    have hlenW : ks.length ≤ source.traceWidth := by
      have hcard := Finset.card_le_card hsub
      rw [List.toFinset_card_of_nodup hks] at hcard
      simpa using hcard
    have hsurvivors : (survivorCols source ks).length =
        source.traceWidth - ks.length := by
      simpa [survivorCols, dropIdxG, hkbelowW] using
        survivor_rank ks hks source.traceWidth
    have hpast : (survivorCols source ks).length ≤ dropIdxG ks c := by
      rw [hsurvivors]
      unfold dropIdxG
      rw [hkbelowC]
      omega
    unfold projectRow
    rw [List.getD_eq_default _ _ hpast]
    unfold dropIdxG
    rw [hkbelowC]
    apply congrArg a
    exact Nat.sub_add_cancel (Nat.le_trans hlenW (Nat.le_of_not_gt hc))

/-- Reverse kept-constraint transport.  This is the source-to-compact companion
of `RotWideCompactS2.holdsAt_transport`; table membership is transported in the
source-to-compact direction supplied by `htbl`. -/
theorem holdsAt_project (hash : List Int -> Int) (g : Nat -> Nat)
    (tfC tfX : TraceFamily) (E EX : VmRowEnv) (isF isL : Bool)
    (c : VmConstraint2)
    (hloc : ∀ r ∈ refs2 c, EX.loc r = E.loc (g r))
    (hnxt : ∀ r ∈ refs2 c, EX.nxt r = E.nxt (g r))
    (hpub : EX.pub = E.pub)
    (htrans : ∀ hi lo, c = .base (.transition hi lo) ->
      g (sbCol hi) = sbCol hi ∧ g (saCol lo) = saCol lo)
    (htbl : ∀ tid : TableId, ∀ row ∈ tfX tid, row ∈ tfC tid)
    (h : c.holdsAt hash tfX EX isF isL) :
    (mapC2 g c).holdsAt hash tfC E isF isL := by
  cases c with
  | base b =>
    cases b with
    | gate body =>
      cases isL with
      | true => trivial
      | false =>
        have heq : (mapVarE g body).eval E.loc = body.eval EX.loc :=
          evalE_map_agree g body E.loc EX.loc
            (fun r hr => hloc r (by simpa [refs2, refsC] using hr))
        simpa only [VmConstraint2.holdsAt, VmConstraint.holdsVm, mapC2, mapC, heq] using h
    | transition hi lo =>
      cases isL with
      | true => trivial
      | false =>
        obtain ⟨h1, h2⟩ := htrans hi lo rfl
        have hn : EX.nxt (sbCol hi) = E.nxt (sbCol hi) := by
          rw [hnxt (sbCol hi) (by simp [refs2, refsC]), h1]
        have hl : EX.loc (saCol lo) = E.loc (saCol lo) := by
          rw [hloc (saCol lo) (by simp [refs2, refsC]), h2]
        simpa only [VmConstraint2.holdsAt, VmConstraint.holdsVm, mapC2, mapC, hn, hl] using h
    | boundary r body =>
      have heq : (mapVarE g body).eval E.loc = body.eval EX.loc :=
        evalE_map_agree g body E.loc EX.loc
          (fun r' hr => hloc r' (by simpa [refs2, refsC] using hr))
      cases r with
      | first =>
        simpa only [VmConstraint2.holdsAt, VmConstraint.holdsVm, mapC2, mapC, heq] using h
      | last =>
        simpa only [VmConstraint2.holdsAt, VmConstraint.holdsVm, mapC2, mapC, heq] using h
    | piBinding r col k =>
      have heq : EX.loc col = E.loc (g col) := hloc col (by simp [refs2, refsC])
      cases r with
      | first =>
        simpa only [VmConstraint2.holdsAt, VmConstraint.holdsVm, mapC2, mapC, heq, hpub] using h
      | last =>
        simpa only [VmConstraint2.holdsAt, VmConstraint.holdsVm, mapC2, mapC, heq, hpub] using h
  | lookup l =>
    show (l.tuple.map (mapVarE g)).map (fun e => e.eval E.loc) ∈ tfC l.table
    have heq : (l.tuple.map (mapVarE g)).map (fun e => e.eval E.loc) =
        l.tuple.map (fun e => e.eval EX.loc) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro e he
      exact evalE_map_agree g e E.loc EX.loc
        (fun r hr => hloc r (by
          simp only [refs2]
          exact List.mem_flatMap.mpr ⟨e, he, hr⟩))
    apply htbl l.table
    rwa [heq]
  | memOp m => trivial
  | umemOp m => trivial
  | proofBind m => trivial
  | mapOp m =>
    intro hguardC
    have hmem0 : ∀ e ∈ [m.guard, m.key, m.value, m.root 0, m.newRoot 0],
        ∀ r ∈ refsE e, EX.loc r = E.loc (g r) := by
      intro e he r hr
      apply hloc
      simp only [refs2, List.mem_append]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl
      · exact Or.inl (Or.inl (Or.inl (Or.inl hr)))
      · exact Or.inl (Or.inl (Or.inl (Or.inr hr)))
      · exact Or.inl (Or.inl (Or.inr hr))
      · exact Or.inl (Or.inr (List.mem_flatMap.mpr
          ⟨m.root 0, List.mem_ofFn.mpr ⟨0, rfl⟩, hr⟩))
      · exact Or.inr (List.mem_flatMap.mpr
          ⟨m.newRoot 0, List.mem_ofFn.mpr ⟨0, rfl⟩, hr⟩)
    have hguardX : m.guard.eval EX.loc = 1 := by
      rw [← evalE_map_agree g m.guard E.loc EX.loc (hmem0 m.guard (by simp))]
      exact hguardC
    have hs := h hguardX
    have hr0 : (mapVarE g (m.root 0)).eval E.loc = (m.root 0).eval EX.loc :=
      evalE_map_agree g _ _ _ (hmem0 (m.root 0) (by simp))
    have hk0 : (mapVarE g m.key).eval E.loc = m.key.eval EX.loc :=
      evalE_map_agree g _ _ _ (hmem0 m.key (by simp))
    have hv0 : (mapVarE g m.value).eval E.loc = m.value.eval EX.loc :=
      evalE_map_agree g _ _ _ (hmem0 m.value (by simp))
    have hn0 : (mapVarE g (m.newRoot 0)).eval E.loc = (m.newRoot 0).eval EX.loc :=
      evalE_map_agree g _ _ _ (hmem0 (m.newRoot 0) (by simp))
    cases hop : m.op <;>
      simp only [mapMapF, hop] at hs ⊢ <;>
      · simp only [hr0, hk0, hv0, hn0]
        exact hs
  | windowGate w =>
    have heq : (mapVarW g w.body).eval E = w.body.eval EX :=
      evalW_map_agree g w.body E EX
        (fun r hr => hloc r (by simpa [refs2] using hr))
        (fun r hr => hnxt r (by simpa [refs2] using hr))
    cases how : w.onTransition <;>
      simp only [VmConstraint2.holdsAt, WindowConstraint.holdsAt, mapC2, how] at h ⊢ <;>
      rwa [heq]

/-- Reverse hash-site transport over an unchanged auxiliary table family. -/
theorem siteHoldsAll_project (hash : List Int -> Int) (E EX : VmRowEnv)
    (g : Nat -> Nat) (sites : List VmHashSite)
    (hagree : ∀ s ∈ sites, ∀ r ∈ refsSite s, EX.loc r = E.loc (g r)) :
    siteHoldsAll hash EX sites -> siteHoldsAll hash E (sites.map (mapSite g)) := by
  suffices hgo : ∀ acc, siteHoldsAll.go hash EX acc sites ->
      siteHoldsAll.go hash E acc (sites.map (mapSite g)) from hgo []
  induction sites with
  | nil => intro acc h; trivial
  | cons s ss ih =>
    intro acc h
    obtain ⟨hd, hrest⟩ := h
    have hres : (mapSite g s).resolvedInputs E acc = s.resolvedInputs EX acc := by
      unfold VmHashSite.resolvedInputs mapSite
      simp only [List.map_map]
      apply List.map_congr_left
      intro input hi
      cases input with
      | col c =>
        simp only [Function.comp_apply, HashInput.resolve]
        exact (hagree s List.mem_cons_self c (by
          unfold refsSite
          exact List.mem_cons_of_mem _
            (List.mem_filterMap.mpr ⟨.col c, hi, rfl⟩))).symm
      | digest k => rfl
      | zero => rfl
    have hdig : EX.loc s.digestCol = E.loc (g s.digestCol) :=
      hagree s List.mem_cons_self s.digestCol (by
        unfold refsSite
        exact List.mem_cons_self)
    refine ⟨?_, ?_⟩
    · change E.loc (g s.digestCol) = _
      rw [← hdig, hres]
      exact hd
    · rw [hres]
      exact ih (fun s' hs' => hagree s' (List.mem_cons_of_mem _ hs')) _ hrest

/-- Row-window agreement for the projected trace, including off-the-end rows. -/
theorem projectTrace_getD (source : EffectVmDescriptor2) (ks : List Nat)
    (hks : ks.Nodup) (hwidth : ∀ k ∈ ks, k < source.traceWidth)
    (t : VmTrace) (i c : Nat) (halive : isKilled ks c = false) :
    (projectTrace source ks t).rows.getD i zeroAsg (dropIdxG ks c) =
      t.rows.getD i zeroAsg c := by
  show (t.rows.map (projectRow source ks)).getD i zeroAsg (dropIdxG ks c) = _
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases hrow : t.rows[i]? with
  | none => rfl
  | some a => exact projectRow_agree_notKilled source ks hks hwidth a c halive

/-- `flatMap` congruence for equal-length row lists related pointwise by index. -/
theorem flatMap_eq_of_getElem {alpha beta gamma : Type}
    (xs : List alpha) (ys : List beta) (F : alpha -> List gamma)
    (G : beta -> List gamma) (hlen : xs.length = ys.length)
    (h : ∀ i (hx : i < xs.length) (hy : i < ys.length), F xs[i] = G ys[i]) :
    xs.flatMap F = ys.flatMap G := by
  induction xs generalizing ys with
  | nil =>
    have : ys = [] := List.eq_nil_of_length_eq_zero hlen.symm
    subst ys
    rfl
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      simp only [List.flatMap_cons]
      have h0 := h 0 (by simp) (by simp)
      simp only [List.getElem_cons_zero] at h0
      rw [h0]
      have htail : xs.flatMap F = ys.flatMap G := by
        apply ih ys hlen
        intro i hx hy
        have hi := h (i + 1) (by simp; omega) (by simp; omega)
        simpa using hi
      rw [htail]

theorem memOp_mem_constraints (source : EffectVmDescriptor2) (m : MemOp)
    (hm : m ∈ memOpsOf source) : .memOp m ∈ source.constraints := by
  obtain ⟨c, hc, hp⟩ := List.mem_filterMap.mp hm
  cases c <;> simp_all [memOpsOf]

theorem mapOp_mem_constraints (source : EffectVmDescriptor2) (m : MapOp)
    (hm : m ∈ mapOpsOf source) : .mapOp m ∈ source.constraints := by
  obtain ⟨c, hc, hp⟩ := List.mem_filterMap.mp hm
  cases c <;> simp_all [mapOpsOf]

/-- Source and compact memory logs coincide under a same-length row projection
that agrees on the source descriptor's live reference surface. -/
theorem memLog_project (source : EffectVmDescriptor2) (ks : List Nat)
    (tX tC : VmTrace) (hlen : tX.rows.length = tC.rows.length)
    (hagree : ∀ i (_hi : i < tX.rows.length) r, r ∈ liveCols source ->
      (envAt tX i).loc r = (envAt tC i).loc (dropIdxG ks r)) :
    memLog source tX = memLog (compactE1 source ks) tC := by
  unfold memLog
  rw [memOpsOf_compactE1]
  apply flatMap_eq_of_getElem tX.rows tC.rows _ _ hlen
  intro i hiX hiC
  apply filterMap_opAt?_map
  intro m hm r hr
  have ha := hagree i hiX r
    (refs2_mem_liveCols source (.memOp m)
      (memOp_mem_constraints source m hm) r hr)
  simpa [envAt, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hiX, List.getElem?_eq_getElem hiC] using ha

/-- Source and compact map-operation logs coincide under the same projection. -/
theorem mapLog_project (source : EffectVmDescriptor2) (ks : List Nat)
    (tX tC : VmTrace) (hlen : tX.rows.length = tC.rows.length)
    (hagree : ∀ i (_hi : i < tX.rows.length) r, r ∈ liveCols source ->
      (envAt tX i).loc r = (envAt tC i).loc (dropIdxG ks r)) :
    mapLog source tX = mapLog (compactE1 source ks) tC := by
  unfold mapLog
  rw [mapOpsOf_compactE1]
  apply flatMap_eq_of_getElem tX.rows tC.rows _ _ hlen
  intro i hiX hiC
  apply filterMap_rowAt_map
  intro m hm r hr
  have ha := hagree i hiX r
    (refs2_mem_liveCols source (.mapOp m)
      (mapOp_mem_constraints source m hm) r hr)
  simpa [envAt, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hiX, List.getElem?_eq_getElem hiC] using ha

/-! Universal-memory transport is separate because `Satisfied2U` extends the
live `Satisfied2` boundary with another ordered log and faithful table. -/

/-- The UMem arm of `mapC2`, named so its log transport can be stated directly. -/
def mapUMemF (g : Nat -> Nat) (m : UMemOp) : UMemOp :=
  { m with
    guard := mapVarE g m.guard
    key := mapVarE g m.key
    present := mapVarE g m.present
    value := mapVarE g m.value
    prevPresent := mapVarE g m.prevPresent
    prevValue := mapVarE g m.prevValue
    prevSerial := mapVarE g m.prevSerial }

theorem umemOpsOf_compactE1 (source : EffectVmDescriptor2) (ks : List Nat) :
    umemOpsOf (compactE1 source ks) =
      (umemOpsOf source).map (mapUMemF (dropIdxG ks)) := by
  show (source.constraints.map (mapC2 (dropIdxG ks))).filterMap _ = _
  unfold umemOpsOf
  induction source.constraints with
  | nil => rfl
  | cons c cs ih => cases c <;> simp [mapC2, mapUMemF, ih]

/-- Per-row universal-memory operation transport. -/
theorem umemOpAt_transport (g : Nat -> Nat) (m : UMemOp)
    (a aX : Dregg2.Circuit.Assignment)
    (hag : ∀ r ∈ refs2 (.umemOp m), aX r = a (g r)) :
    UMemOp.opAt? aX m = UMemOp.opAt? a (mapUMemF g m) := by
  have hfield : ∀ e ∈ [m.guard, m.key, m.present, m.value,
      m.prevPresent, m.prevValue, m.prevSerial],
      (mapVarE g e).eval a = e.eval aX := by
    intro e he
    apply evalE_map_agree g e a aX
    intro r hr
    apply hag
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    simp only [refs2, List.mem_append]
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hr)))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hr)))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hr))))
    · exact Or.inl (Or.inl (Or.inl (Or.inr hr)))
    · exact Or.inl (Or.inl (Or.inr hr))
    · exact Or.inl (Or.inr hr)
    · exact Or.inr hr
  unfold UMemOp.opAt? mapUMemF
  simp only [hfield m.guard (by simp), hfield m.key (by simp),
    hfield m.present (by simp), hfield m.value (by simp),
    hfield m.prevPresent (by simp), hfield m.prevValue (by simp),
    hfield m.prevSerial (by simp)]

theorem filterMap_umemOpAt_map (g : Nat -> Nat)
    (a aX : Dregg2.Circuit.Assignment) (ops : List UMemOp)
    (hag : ∀ m ∈ ops, ∀ r ∈ refs2 (.umemOp m), aX r = a (g r)) :
    ops.filterMap (UMemOp.opAt? aX) =
      (ops.map (mapUMemF g)).filterMap (UMemOp.opAt? a) := by
  induction ops with
  | nil => rfl
  | cons m ms ih =>
    rw [List.map_cons, List.filterMap_cons, List.filterMap_cons,
      umemOpAt_transport g m a aX (hag m List.mem_cons_self),
      ih (fun m' hm' => hag m' (List.mem_cons_of_mem _ hm'))]

theorem umemOp_mem_constraints (source : EffectVmDescriptor2) (m : UMemOp)
    (hm : m ∈ umemOpsOf source) : .umemOp m ∈ source.constraints := by
  obtain ⟨c, hc, hp⟩ := List.mem_filterMap.mp hm
  cases c <;> simp_all [umemOpsOf]

/-- Source and compact universal-memory logs coincide under the same live-column
projection used by the base descriptor. -/
theorem umemLog_project (source : EffectVmDescriptor2) (ks : List Nat)
    (tX tC : VmTrace) (hlen : tX.rows.length = tC.rows.length)
    (hagree : ∀ i (_hi : i < tX.rows.length) r, r ∈ liveCols source ->
      (envAt tX i).loc r = (envAt tC i).loc (dropIdxG ks r)) :
    umemLog source tX = umemLog (compactE1 source ks) tC := by
  unfold umemLog
  rw [umemOpsOf_compactE1]
  apply flatMap_eq_of_getElem tX.rows tC.rows _ _ hlen
  intro i hiX hiC
  apply filterMap_umemOpAt_map
  intro m hm r hr
  have ha := hagree i hiX r
    (refs2_mem_liveCols source (.umemOp m)
      (umemOp_mem_constraints source m hm) r hr)
  simpa [envAt, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hiX, List.getElem?_eq_getElem hiC] using ha

/-- Expansion also commutes with the universal-memory log. -/
theorem umemLog_expandG (source : EffectVmDescriptor2) (ks : List Nat) (t : VmTrace) :
    umemLog source (expandTraceG ks t) = umemLog (compactE1 source ks) t := by
  unfold umemLog
  rw [umemOpsOf_compactE1]
  show (t.rows.map (expandRowG ks)).flatMap _ = _
  apply flatMap_map_rows
  intro a
  apply filterMap_umemOpAt_map
  intro m hm r hr
  rfl

/-- Generic reverse E1 bridge.  A source witness projects to a compact witness
when row count, public assignment, auxiliary tables, and all live-column values
are preserved. -/
theorem compactE1_project (hash : List Int -> Int)
    (source : EffectVmDescriptor2) (ks : List Nat)
    (minit : Int -> Int) (mfin : Int -> Int × Nat) (maddrs : List Int)
    (tX tC : VmTrace) (hok : compactE1Ok source ks = true)
    (hlen : tX.rows.length = tC.rows.length) (hpub : tX.pub = tC.pub)
    (htf : tX.tf = tC.tf)
    (hagree : ∀ i r, r ∈ liveCols source ->
      (envAt tX i).loc r = (envAt tC i).loc (dropIdxG ks r))
    (hsat : Satisfied2 hash source minit mfin maddrs tX) :
    Satisfied2 hash (compactE1 source ks) minit mfin maddrs tC := by
  unfold compactE1Ok at hok
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨hkeptAll, _hsitesOk⟩, _hrangesOk⟩, _hnodup⟩, _hwidth⟩ := hok
  set g := dropIdxG ks with hg
  have htransOf : ∀ c ∈ source.constraints, ∀ hi lo,
      c = .base (.transition hi lo) ->
      g (sbCol hi) = sbCol hi ∧ g (saCol lo) = saCol lo := by
    intro c hc hi lo hceq
    have hk := hkeptAll c hc
    unfold keptOkG at hk
    subst hceq
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hk
    obtain ⟨-, hbelow⟩ := hk
    refine ⟨dropIdxG_id_of_low ks _ ?_, dropIdxG_id_of_low ks _ ?_⟩
    · intro k hkm; have := hbelow k hkm; omega
    · intro k hkm; have := hbelow k hkm; omega
  have htbl : ∀ tid : TableId, ∀ row ∈ tX.tf tid, row ∈ tC.tf tid := by
    intro tid row hrow
    rw [← htf]
    exact hrow
  have hml : memLog source tX = memLog (compactE1 source ks) tC :=
    memLog_project source ks tX tC hlen (fun i _ r hr => hagree i r hr)
  have hmpl : mapLog source tX = mapLog (compactE1 source ks) tC :=
    mapLog_project source ks tX tC hlen (fun i _ r hr => hagree i r hr)
  refine ⟨?_, ?_, ?_, hsat.memAddrsNodup, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hiC cC hcC
    change cC ∈ source.constraints.map (mapC2 g) at hcC
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hcC
    have hiX : i < tX.rows.length := by rw [hlen]; exact hiC
    have hsource := hsat.rowConstraints i hiX c hc
    rw [hlen] at hsource
    exact holdsAt_project hash g tC.tf tX.tf (envAt tC i) (envAt tX i)
      (i == 0) (i + 1 == tC.rows.length) c
      (fun r hr => hagree i r (refs2_mem_liveCols source c hc r hr))
      (fun r hr => hagree (i + 1) r (refs2_mem_liveCols source c hc r hr))
      hpub (htransOf c hc) htbl hsource
  · intro i hiC
    have hiX : i < tX.rows.length := by rw [hlen]; exact hiC
    change siteHoldsAll hash (envAt tC i) (source.hashSites.map (mapSite g))
    exact siteHoldsAll_project hash (envAt tC i) (envAt tX i) g source.hashSites
      (fun s hs r hr => hagree i r (refsSite_mem_liveCols source s hs r hr))
      (hsat.rowHashes i hiX)
  · intro i hiC rC hrC
    change rC ∈ source.ranges.map (mapRange g) at hrC
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hrC
    have hiX : i < tX.rows.length := by rw [hlen]; exact hiC
    have hsource := hsat.rowRanges i hiX r hr
    unfold VmRange.holds at hsource ⊢
    simp only [mapRange]
    rw [← hagree i r.wire (range_wire_mem_liveCols source r hr)]
    exact hsource
  · rw [← hml]
    exact hsat.memClosed
  · rw [← hml]
    exact hsat.memDisciplined
  · rw [← hml]
    exact hsat.memBalanced
  · rw [← htf, ← hml]
    exact hsat.memTableFaithful
  · rw [← htf, ← hmpl]
    exact hsat.mapTableFaithful

/-- Reverse E1 transport for the universal-memory extension.  Its ordered UMem
log and `.custom UMEM_TID` table are carried by exact equality, in addition to
all base `Satisfied2` legs. -/
theorem compactE1_projectU (hash : List Int -> Int)
    (source : EffectVmDescriptor2) (ks : List Nat)
    (minit : Int -> Int) (mfin : Int -> Int × Nat) (maddrs : List Int)
    (uinit : Dregg2.Crypto.UniversalMemory.UAddr Int -> Option Int)
    (ufin : Dregg2.Crypto.UniversalMemory.UAddr Int -> Option Int × Nat)
    (uaddrs : List (Dregg2.Crypto.UniversalMemory.UAddr Int))
    (tX tC : VmTrace) (hok : compactE1Ok source ks = true)
    (hlen : tX.rows.length = tC.rows.length) (hpub : tX.pub = tC.pub)
    (htf : tX.tf = tC.tf)
    (hagree : ∀ i r, r ∈ liveCols source ->
      (envAt tX i).loc r = (envAt tC i).loc (dropIdxG ks r))
    (hsat : Satisfied2U hash source minit mfin maddrs
      uinit ufin uaddrs tX) :
    Satisfied2U hash (compactE1 source ks) minit mfin maddrs
      uinit ufin uaddrs tC := by
  have hbase := compactE1_project hash source ks minit mfin maddrs
    tX tC hok hlen hpub htf hagree hsat.toSatisfied2
  have huml : umemLog source tX = umemLog (compactE1 source ks) tC :=
    umemLog_project source ks tX tC hlen (fun i _ r hr => hagree i r hr)
  refine
    { toSatisfied2 := hbase
      umemAddrsNodup := hsat.umemAddrsNodup
      umemClosed := ?_
      umemDisciplined := ?_
      umemBalanced := ?_
      umemNullifierInsertOnly := ?_
      umemTableFaithful := ?_ }
  · rw [← huml]
    exact hsat.umemClosed
  · rw [← huml]
    exact hsat.umemDisciplined
  · rw [← huml]
    exact hsat.umemBalanced
  · rw [← huml]
    exact hsat.umemNullifierInsertOnly
  · rw [← htf, ← huml]
    exact hsat.umemTableFaithful

/-- Forward E1 expansion also transports every universal-memory leg. -/
theorem compactE1_expandU (hash : List Int -> Int)
    (source : EffectVmDescriptor2) (ks : List Nat)
    (minit : Int -> Int) (mfin : Int -> Int × Nat) (maddrs : List Int)
    (uinit : Dregg2.Crypto.UniversalMemory.UAddr Int -> Option Int)
    (ufin : Dregg2.Crypto.UniversalMemory.UAddr Int -> Option Int × Nat)
    (uaddrs : List (Dregg2.Crypto.UniversalMemory.UAddr Int))
    (t : VmTrace) (hok : compactE1Ok source ks = true)
    (hsat : Satisfied2U hash (compactE1 source ks) minit mfin maddrs
      uinit ufin uaddrs t) :
    Satisfied2U hash source minit mfin maddrs uinit ufin uaddrs
      (expandTraceG ks t) := by
  have hbase := compactE1_expand hash source ks minit mfin maddrs
    t hok hsat.toSatisfied2
  have huml : umemLog source (expandTraceG ks t) =
      umemLog (compactE1 source ks) t := umemLog_expandG source ks t
  refine
    { toSatisfied2 := hbase
      umemAddrsNodup := hsat.umemAddrsNodup
      umemClosed := ?_
      umemDisciplined := ?_
      umemBalanced := ?_
      umemNullifierInsertOnly := ?_
      umemTableFaithful := ?_ }
  · rw [huml]
    exact hsat.umemClosed
  · rw [huml]
    exact hsat.umemDisciplined
  · rw [huml]
    exact hsat.umemBalanced
  · rw [huml]
    exact hsat.umemNullifierInsertOnly
  · change t.tf (.custom UMEM_TID) = _
    rw [huml]
    exact hsat.umemTableFaithful

/-- The derived-kill-set instance of the shared passive pass.  `pass` and its
one-way `security` proof come from the contracts module; the derived adapter
only discharges the full `compactE1Ok` gate from the cheap transition-ceiling
certificate the emit path already carries. -/
def derivedPass (source : EffectVmDescriptor2) (floor : Nat) :
    PassiveOptimization source (compactE1 source (deadColsE1 source floor)) :=
  Dregg2.Circuit.PassiveDescriptorOptimization.E1.pass source
    (deadColsE1 source floor)

theorem derivedSecurity (source : EffectVmDescriptor2) (floor : Nat)
    (hceiling : transitionCeilingOk source floor = true) :
    SecurityRefinement (derivedPass source floor) :=
  Dregg2.Circuit.PassiveDescriptorOptimization.E1.security source
    (deadColsE1 source floor) (compactE1Ok_of_ceiling source floor hceiling)

/-- By construction, a live source column is not in the derived dead-column
set. -/
theorem derived_live_notKilled (source : EffectVmDescriptor2) (floor r : Nat)
    (hr : r ∈ liveCols source) :
    isKilled (deadColsE1 source floor) r = false := by
  unfold isKilled
  simp only [List.contains_eq_mem, decide_eq_false_iff_not]
  intro hkilled
  exact deadColsE1_unref source floor r hkilled hr

/-- Completeness for the derived E1 kill-set.  The canonical projection keeps
row count, public assignment, and every auxiliary table exactly; the derived
unreferencedness theorem supplies agreement on every constraint/hash/range and
memory/map-log column. -/
theorem checkedDerived_complete (source : EffectVmDescriptor2) (floor : Nat)
    (hceiling : transitionCeilingOk source floor = true)
    (hash : List Int -> Int) (minit : Int -> Int)
    (mfin : Int -> Int × Nat) (maddrs : List Int) (t : VmTrace)
    (hsat : Satisfied2 hash source minit mfin maddrs t) :
    Satisfied2 hash (compactE1 source (deadColsE1 source floor))
      minit mfin maddrs (projectTrace source (deadColsE1 source floor) t) := by
  apply compactE1_project hash source (deadColsE1 source floor)
    minit mfin maddrs t (projectTrace source (deadColsE1 source floor) t)
    (compactE1Ok_of_ceiling source floor hceiling)
  · simp [projectTrace]
  · rfl
  · rfl
  · intro i r hr
    exact (projectTrace_getD source (deadColsE1 source floor)
      (deadColsE1_nodup source floor)
      (fun k hk => deadColsE1_lt_width source floor k hk)
      t i r (derived_live_notKilled source floor r hr)).symm
  · exact hsat

/-- Existential satisfaction for the universal-memory extension. -/
def SatisfiableU (hash : List Int -> Int) (d : EffectVmDescriptor2)
    (minit : Int -> Int) (mfin : Int -> Int × Nat) (maddrs : List Int)
    (uinit : Dregg2.Crypto.UniversalMemory.UAddr Int -> Option Int)
    (ufin : Dregg2.Crypto.UniversalMemory.UAddr Int -> Option Int × Nat)
    (uaddrs : List (Dregg2.Crypto.UniversalMemory.UAddr Int)) : Prop :=
  Exists fun t => Satisfied2U hash d minit mfin maddrs uinit ufin uaddrs t

/-- Derived E1 completeness including the universal-memory ordered log,
insert-only condition, balance, and faithful UMem table. -/
theorem checkedDerived_completeU (source : EffectVmDescriptor2) (floor : Nat)
    (hceiling : transitionCeilingOk source floor = true)
    (hash : List Int -> Int) (minit : Int -> Int)
    (mfin : Int -> Int × Nat) (maddrs : List Int)
    (uinit : Dregg2.Crypto.UniversalMemory.UAddr Int -> Option Int)
    (ufin : Dregg2.Crypto.UniversalMemory.UAddr Int -> Option Int × Nat)
    (uaddrs : List (Dregg2.Crypto.UniversalMemory.UAddr Int))
    (t : VmTrace)
    (hsat : Satisfied2U hash source minit mfin maddrs
      uinit ufin uaddrs t) :
    Satisfied2U hash (compactE1 source (deadColsE1 source floor))
      minit mfin maddrs uinit ufin uaddrs
      (projectTrace source (deadColsE1 source floor) t) := by
  apply compactE1_projectU hash source (deadColsE1 source floor)
    minit mfin maddrs uinit ufin uaddrs
    t (projectTrace source (deadColsE1 source floor) t)
    (compactE1Ok_of_ceiling source floor hceiling)
  · simp [projectTrace]
  · rfl
  · rfl
  · intro i r hr
    exact (projectTrace_getD source (deadColsE1 source floor)
      (deadColsE1_nodup source floor)
      (fun k hk => deadColsE1_lt_width source floor k hk)
      t i r (derived_live_notKilled source floor r hr)).symm
  · exact hsat

/-- The universal-memory extension is also equisatisfiable across the derived
E1 pass. -/
theorem checkedDerived_satisfiableU_iff
    (source : EffectVmDescriptor2) (floor : Nat)
    (hceiling : transitionCeilingOk source floor = true)
    (hash : List Int -> Int) (minit : Int -> Int)
    (mfin : Int -> Int × Nat) (maddrs : List Int)
    (uinit : Dregg2.Crypto.UniversalMemory.UAddr Int -> Option Int)
    (ufin : Dregg2.Crypto.UniversalMemory.UAddr Int -> Option Int × Nat)
    (uaddrs : List (Dregg2.Crypto.UniversalMemory.UAddr Int)) :
    SatisfiableU hash source minit mfin maddrs uinit ufin uaddrs <->
      SatisfiableU hash (compactE1 source (deadColsE1 source floor))
        minit mfin maddrs uinit ufin uaddrs := by
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨projectTrace source (deadColsE1 source floor) t,
      checkedDerived_completeU source floor hceiling hash minit mfin maddrs
        uinit ufin uaddrs t ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨expandTraceG (deadColsE1 source floor) t,
      compactE1_expandU hash source (deadColsE1 source floor)
        minit mfin maddrs uinit ufin uaddrs t
        (compactE1Ok_of_ceiling source floor hceiling) ht⟩

/-- `checkedDerived_complete` is exactly the framework's completeness contract
for the derived E1 pass. -/
theorem derivedCompleteness (source : EffectVmDescriptor2) (floor : Nat)
    (hceiling : transitionCeilingOk source floor = true) :
    CompletenessPreservation (derivedPass source floor) := by
  intro hash minit mfin maddrs t hsat
  exact checkedDerived_complete source floor hceiling hash minit mfin maddrs t hsat

/-- The performance-relevant derived E1 adapter is exact: the landed expansion
is the security direction and `checkedDerived_complete` supplies the
source-to-compact witness construction.  This is the upgrade the contracts
module points at — the E1 pass is not merely a one-way security refinement. -/
theorem derivedPreservation (source : EffectVmDescriptor2) (floor : Nat)
    (hceiling : transitionCeilingOk source floor = true) :
    SatisfiabilityPreservation (derivedPass source floor) :=
  ⟨derivedSecurity source floor hceiling, derivedCompleteness source floor hceiling⟩

/-- E1's derived dead-column deletion therefore preserves existential
satisfiability in both directions at every unchanged external boundary. -/
theorem checkedDerived_satisfiable_iff
    (source : EffectVmDescriptor2) (floor : Nat)
    (hceiling : transitionCeilingOk source floor = true)
    (hash : List Int -> Int) (minit : Int -> Int)
    (mfin : Int -> Int × Nat) (maddrs : List Int) :
    Satisfiable hash source minit mfin maddrs <->
      Satisfiable hash (compactE1 source (deadColsE1 source floor))
        minit mfin maddrs :=
  satisfiable_iff_of_preservation (derivedPreservation source floor hceiling)
    hash minit mfin maddrs

theorem checkedDerived_target_satisfiable_implies_source
    (source : EffectVmDescriptor2) (floor : Nat)
    (hceiling : transitionCeilingOk source floor = true)
    (hash : List Int -> Int) (minit : Int -> Int)
    (mfin : Int -> Int × Nat) (maddrs : List Int) :
    Satisfiable hash (compactE1 source (deadColsE1 source floor))
        minit mfin maddrs ->
      Satisfiable hash source minit mfin maddrs :=
  security_target_witness_implies_source
    (derivedSecurity source floor hceiling) hash minit mfin maddrs

/-- The derived pass also transports every auxiliary table and the row count
exactly, which `Satisfied2` alone would not give. -/
theorem derivedExactCarriers (source : EffectVmDescriptor2) (floor : Nat) :
    ExactCarrierTransport (derivedPass source floor) :=
  Dregg2.Circuit.PassiveDescriptorOptimization.E1.exactCarriers source
    (deadColsE1 source floor)

end E1

#assert_axioms eraseName_satisfied_iff
#assert_axioms eraseNamePreservation
#assert_axioms eraseName_satisfiable_iff
#assert_axioms E1.derivedSecurity
#assert_axioms E1.derivedCompleteness
#assert_axioms E1.derivedPreservation
#assert_axioms E1.checkedDerived_target_satisfiable_implies_source
#assert_axioms E1.checkedDerived_complete
#assert_axioms E1.checkedDerived_satisfiable_iff
#assert_axioms E1.checkedDerived_completeU
#assert_axioms E1.checkedDerived_satisfiableU_iff

end Dregg2.Metatheory.EffectVmDescriptor2PassiveOptimization

/-
# Dregg2.Circuit.Emit.EffectVmEmitSetFieldFullState — setField LIFTED to FULL-STATE on the RUNNABLE
descriptor (the magnesium breadth: the circuit the prover RUNS binds all 17 fields).

`EffectVmEmitSetField` reaches per-cell CLASS A on the 186-wide RUNNABLE descriptor: the written field
column `fields[slot]` is among the 13 absorbed columns, so the move is bound + anti-ghosted by the
injective-commitment tooth (`setFieldDescriptor_classA`). But that `state_commit` absorbs only the 13
state-block columns, NOT the 8 side-table roots. This module CLOSES that by amplifying the per-slot
RUNNABLE descriptor to the WIDE (`system_roots`-absorbing) shape and lifting through the generic
`EffectVmFullStateRunnable.runnable_full_sound` crown: a satisfying WIDE-descriptor witness pins the FULL
17-field declarative post-state — the per-cell field-write block (`CellSetFieldSpec`: `fields[slot]`
written, every other column frozen) AND every one of the 8 side-table roots FROZEN (setField touches no
side-table). The anti-ghost tooth bites on all 17 (incl. any root).

The §RECIPE applied to setField (a per-slot family — one instance per `slot : Fin 8`). The "written
value" is read off `post.fields slot` (the `RowEncodesSF` clause `env.loc (prmCol VALUE) =
post.fields slot` ties the value carrier to it), so the clause is env-free + non-vacuous.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR only via the generic theorems.
No `sorry`/`:= True`/`native_decide`. `fullClause` NON-VACUOUS. Read-only imports; owns only itself.
-/
import Dregg2.Circuit.Emit.EffectVmEmitSetField
import Dregg2.Circuit.Emit.EffectVmFullStateRunnable

namespace Dregg2.Circuit.Emit.EffectVmEmitSetFieldFullState

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState absorbedCols)
open Dregg2.Circuit.Emit.EffectVmEmitSetField
  (SEL_SET_FIELD VALUE IsSetFieldRow setFieldRowGates setFieldVmDescriptor RowEncodesSF CellSetFieldSpec
   setFieldVm_faithful intent_to_cellSpec)
open Dregg2.Circuit.Emit.EffectVmFullStateRunnable
  (RunnableFullStateSpec runnable_full_sound runnable_full_commit_binds wide_rejects_root_tamper
   wideHashSites)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.SystemRoots (SysRoots systemRootsDigest emptySystemRoots N_SYSTEM_ROOTS)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §1 — the WIDE setField descriptor (per slot; width + sites; constraints UNCHANGED).

`setFieldVmDescriptor slot` carries ONLY `setFieldRowGates slot` (no transition/boundary/selector), with
`hashSites := transferHashSites`. The wide form swaps in `EFFECT_VM_WIDTH_SYSROOTS` + `wideHashSites`. -/

def setFieldVmDescriptorWide (slot : Fin 8) : EffectVmDescriptor :=
  { setFieldVmDescriptor slot with
    name := (setFieldVmDescriptor slot).name ++ "-sysroots"
    traceWidth := EFFECT_VM_WIDTH_SYSROOTS
    hashSites := wideHashSites }

theorem setFieldWide_constraints_eq (slot : Fin 8) :
    (setFieldVmDescriptorWide slot).constraints = (setFieldVmDescriptor slot).constraints := rfl

/-! ## §2 — the GATE-ONLY per-cell soundness (no hash-site hypothesis — the THIN per-effect content).

`setFieldVmDescriptor slot`'s constraints ARE `setFieldRowGates slot`, so the per-row gates are the WHOLE
constraint list (membership is direct). All gates are `.gate`, flag-free. The written value is read off
`post.fields slot` via the `RowEncodesSF` value-carrier clause. -/

theorem setFieldGates_give_cellSpec (slot : Fin 8) (env : VmRowEnv) (pre post : CellState)
    (henc : RowEncodesSF slot env pre post)
    (hgates : ∀ c ∈ (setFieldVmDescriptor slot).constraints, c.holdsVm env true true) :
    CellSetFieldSpec slot pre (post.fields slot) post := by
  -- the per-row gates are the whole constraint list; restrict to the flag-free `false false` form.
  have hrowgates : ∀ c ∈ setFieldRowGates slot, c.holdsVm env false false := by
    intro c hc
    have hh := hgates c hc
    -- every constraint is a `.gate`; `holdsVm` of a gate ignores the flags.
    unfold setFieldRowGates at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    -- dispatch on which gate (the 6 named + the filtered `gOtherFieldsAll` map).
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | hc <;>
      first
        | simpa only [VmConstraint.holdsVm] using hh
        | · -- the `gOtherFieldsAll slot` map members
            simp only [Dregg2.Circuit.Emit.EffectVmEmitSetField.gOtherFieldsAll, List.mem_map,
              List.mem_filter] at hc
            obtain ⟨i, _, rfl⟩ := hc
            simpa only [VmConstraint.holdsVm] using hh
  -- the value carrier IS `post.fields slot` (`RowEncodesSF`), so `intent_to_cellSpec`'s conclusion
  -- `CellSetFieldSpec slot pre (env.loc (prmCol VALUE)) post` rewrites to the env-free written value.
  have hval : env.loc (prmCol VALUE) = post.fields slot := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hVal, _, _⟩ := henc
    exact hVal
  have := intent_to_cellSpec slot env pre post henc ((setFieldVm_faithful slot env).mp hrowgates)
  rw [hval] at this
  exact this

/-! ## §3 — the FULL declarative clause + the `RunnableFullStateSpec` instance (per slot). -/

/-- **`SetFieldFullClause slot`** — the FULL 17-field declarative post for a slot-`slot` setField:
`CellSetFieldSpec slot pre (post.fields slot) post` (the slot written, every other column frozen) AND the
`system_roots` sub-block FROZEN. NON-VACUOUS. -/
def SetFieldFullClause (slot : Fin 8) (preRoots : SysRoots)
    (pre post : CellState) (postRoots : SysRoots) : Prop :=
  CellSetFieldSpec slot pre (post.fields slot) post ∧ postRoots = preRoots

/-- **`setFieldRunnableSpec slot`** — the FULL-state RUNNABLE instance for slot-`slot` setField. THIN;
NON-VACUOUS. -/
def setFieldRunnableSpec (slot : Fin 8) (preRoots : SysRoots) : RunnableFullStateSpec CellState where
  descriptor    := setFieldVmDescriptorWide slot
  usesWideSites := rfl
  isRow         := IsSetFieldRow
  decodeAfter   := fun env pre post postRoots =>
    RowEncodesSF slot env pre post ∧ postRoots = preRoots
  fullClause    := SetFieldFullClause slot preRoots
  decodeFull    := by
    intro env pre post postRoots hrow hdec hgates
    obtain ⟨henc, hroots⟩ := hdec
    exact ⟨setFieldGates_give_cellSpec slot env pre post henc
            (setFieldWide_constraints_eq slot ▸ hgates), hroots⟩

/-! ## §4 — THE DELIVERABLE: `setField_runnable_full_sound`. -/

/-- **`setField_runnable_full_sound` — the magnesium crown for setField.** A row satisfying the WIDE
RUNNABLE slot-`slot` setField descriptor, decoded by `RowEncodesSF` with the frozen-roots witness, pins
the FULL 17-field post-state: the per-cell field-write block (`CellSetFieldSpec`) AND all 8 side-table
roots FROZEN. -/
theorem setField_runnable_full_sound (slot : Fin 8) (hash : List ℤ → ℤ) (preRoots : SysRoots)
    (env : VmRowEnv) (pre post : CellState) (postRoots : SysRoots)
    (hrow : IsSetFieldRow env)
    (henc : RowEncodesSF slot env pre post) (hroots : postRoots = preRoots)
    (hsat : satisfiedVm hash (setFieldVmDescriptorWide slot) env true true) :
    CellSetFieldSpec slot pre (post.fields slot) post ∧ postRoots = preRoots :=
  runnable_full_sound (setFieldRunnableSpec slot preRoots) hash env pre post postRoots hrow
    ⟨henc, hroots⟩ hsat

/-! ## §5 — THE ANTI-GHOST. -/

theorem setField_runnable_full_commit_binds (slot : Fin 8) (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash) (preRoots : SysRoots) (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash (setFieldVmDescriptorWide slot) e₁ true true)
    (hsat₂ : satisfiedVm hash (setFieldVmDescriptorWide slot) e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂) :
    absorbedCols e₁ = absorbedCols e₂ ∧ (∀ i : Fin N_SYSTEM_ROOTS, sr₁ i = sr₂ i) :=
  runnable_full_commit_binds (setFieldRunnableSpec slot preRoots) hash hCR e₁ e₂ sr₁ sr₂
    hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂

/-- **`setField_rejects_root_tamper` — the side-table anti-ghost tooth.** Two wide slot-`slot` setField
rows publishing the same `NEW_COMMIT` (with `systemRootsDigest` carriers) but whose side-table sub-blocks
DIFFER at some root index cannot both satisfy. -/
theorem setField_rejects_root_tamper (slot : Fin 8) (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (preRoots : SysRoots) (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash (setFieldVmDescriptorWide slot) e₁ true true)
    (hsat₂ : satisfiedVm hash (setFieldVmDescriptorWide slot) e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    {i : Fin N_SYSTEM_ROOTS} (htamper : sr₁ i ≠ sr₂ i) : False :=
  wide_rejects_root_tamper (setFieldRunnableSpec slot preRoots) hash hCR e₁ e₂ sr₁ sr₂
    hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂ htamper

/-! ## §6 — NON-VACUITY (slot 0). -/

def setFieldPreRoots : SysRoots := emptySystemRoots

/-- The pre-state: bal_lo 100, all fields 0. -/
def setFieldPre : CellState :=
  { balLo := 100, balHi := 0, nonce := 5, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }

/-- The post-state: `fields[0] := 7` (the written value), everything else frozen. -/
def setFieldPost : CellState :=
  { balLo := 100, balHi := 0, nonce := 5, fields := fun i => if i = 0 then 7 else 0
  , capRoot := 0, reserved := 0, commit := 0 }

/-- **NON-VACUITY (witness TRUE).** The setField `fullClause` (slot 0) is inhabited by a real field
write: `setFieldPost` writes `fields[0] := 7` (= `setFieldPost.fields 0`), every other column frozen,
roots frozen. -/
theorem goodSetField_realizes :
    (setFieldRunnableSpec 0 setFieldPreRoots).fullClause setFieldPre setFieldPost setFieldPreRoots := by
  refine ⟨⟨?_, rfl, rfl, rfl, rfl, rfl, ?_⟩, rfl⟩
  · show setFieldPost.fields 0 = setFieldPost.fields 0; rfl
  · intro i hi
    show setFieldPost.fields i = setFieldPre.fields i
    simp only [setFieldPost, setFieldPre, if_neg hi]

/-- **NON-VACUITY (witness FALSE).** A forged post that MOVES the balance (`100 → 999`) FAILS the clause
(the field-write freezes the balance). -/
theorem setField_clause_not_trivial :
    ¬ SetFieldFullClause 0 setFieldPreRoots setFieldPre { setFieldPost with balLo := 999 } setFieldPreRoots := by
  rintro ⟨⟨_, hbal, _, _, _, _, _⟩, _⟩
  simp only [setFieldPre] at hbal
  norm_num at hbal

/-- **NON-VACUITY (side-table dimension).** A post whose `system_roots` sub-block is NOT the frozen
reference FAILS the clause — the frozen-roots leg is genuine. -/
theorem setField_clause_rejects_root_drop :
    ¬ SetFieldFullClause 0 setFieldPreRoots setFieldPre setFieldPost
        (fun i => if i = (⟨0, by decide⟩ : Fin N_SYSTEM_ROOTS) then 1 else 0) := by
  rintro ⟨_, hroots⟩
  have h0 := congrFun hroots (⟨0, by decide⟩ : Fin N_SYSTEM_ROOTS)
  simp only [setFieldPreRoots, emptySystemRoots] at h0
  norm_num at h0

/-! ## §7 — layout + axiom-hygiene tripwires. -/

#guard (setFieldVmDescriptorWide 0).traceWidth == 188
#guard (setFieldVmDescriptorWide 0).hashSites.length == 4
#guard (setFieldVmDescriptorWide 0).constraints.length == (setFieldVmDescriptor 0).constraints.length

#assert_axioms setFieldGates_give_cellSpec
#assert_axioms setField_runnable_full_sound
#assert_axioms setField_runnable_full_commit_binds
#assert_axioms setField_rejects_root_tamper
#assert_axioms goodSetField_realizes
#assert_axioms setField_clause_not_trivial
#assert_axioms setField_clause_rejects_root_drop

end Dregg2.Circuit.Emit.EffectVmEmitSetFieldFullState

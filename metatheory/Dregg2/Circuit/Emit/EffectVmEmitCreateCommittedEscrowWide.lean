/-
# Dregg2.Circuit.Emit.EffectVmEmitCreateCommittedEscrowWide — the createCommittedEscrow (and its
createObligation dispatch-alias) RUNNABLE descriptor lifted to FULL-STATE (the magnesium breadth).

`EffectVmEmitCreateCommittedEscrow` proved the committed-escrow CREATE per-cell soundness
(`escrowCreateVm_faithful` + `intent_to_cellEscrowSpec` ⇒ `CellEscrowSpec`: the `balLo` DEBIT by `amount`,
the whole frame frozen, nonce frozen) and bound the `escrows` root via the RAW carrier `96`. This module
re-targets it onto the DEDICATED `sysRootsDigestCol` (= 186) via the shared `EffectVmEmitEscrowFamilyWide`
builder and lifts it through the generic crown: `committedEscrow_runnable_full_sound` — a satisfying
witness of the WIDE RUNNABLE descriptor pins the FULL 17-field declarative post-state. The
NO-MALLEABILITY teeth follow from the generic anti-ghost.

This descriptor (`escrowCreateVmDescriptorGenuine`'s row gates) is the one `createObligation` is
dispatch-aliased to (`Argus/Effects/CreateObligation.lean`: `createObligationStmt = createEscrowStmt …`,
`createObligationA ↦ createEscrowChainA`), so createObligation inherits this full-state binding through
the SAME wide descriptor — no separate circuit.

## Honesty
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY through the named
`Poseidon2SpongeCR` carrier inside the generic crown's anti-ghost. No `sorry`/`:= True`/`native_decide`.
This module OWNS only itself; every import is read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitEscrowFamilyWide
import Dregg2.Circuit.Emit.EffectVmEmitCreateCommittedEscrow

namespace Dregg2.Circuit.Emit.EffectVmEmitCreateCommittedEscrowWide

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState absorbedCols)
open Dregg2.Circuit.Emit.EffectVmEmitCreateCommittedEscrow
  (escrowCreateRowGates escrowCreateVmAirName IsEscrowCreateRow RowEncodesEscrow CellEscrowSpec
   EscrowParams intent_to_cellEscrowSpec escrowCreateVm_faithful gBalLoDebit gNonceFreeze)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gBalHi gCapPass gResPass gFieldPass gFieldPassAll)
open Dregg2.Circuit.Emit.EffectVmEmitEscrowFamilyWide
  (escrowFamilyWideDescriptor escrowFamilyWideSpec escrow_family_runnable_full_sound
   escrowFamily_binds_full_state EscrowFamilyFullClause ESCROW_STEP_PARAM ESCROW_ROOT_INDEX)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.SystemRoots (SysRoots systemRootsDigest N_SYSTEM_ROOTS emptySystemRoots)

set_option linter.unusedVariables false

/-! ## §1 — the row gates are all `.gate`s + the per-cell gate-soundness. -/

theorem escrowCreateRowGates_allGate : ∀ g ∈ escrowCreateRowGates, ∃ b, g = .gate b := by
  intro g hg
  unfold escrowCreateRowGates gFieldPassAll at hg
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_range] at hg
  rcases hg with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
  · exact ⟨gBalLoDebit, rfl⟩
  · exact ⟨gBalHi, rfl⟩
  · exact ⟨gNonceFreeze, rfl⟩
  · exact ⟨gCapPass, rfl⟩
  · exact ⟨gResPass, rfl⟩
  · exact ⟨gFieldPass i, rfl⟩

/-- **`committedEscrow_cellFromGates`** — the committed-escrow row gates (flag-free), decoded by
`RowEncodesEscrow`, force `CellEscrowSpec` (the DEBIT + frame freeze). NEITHER reads a hash-site. -/
theorem committedEscrow_cellFromGates (p : EscrowParams) (env : VmRowEnv) (pre post : CellState)
    (hrow : IsEscrowCreateRow env) (henc : RowEncodesEscrow env pre p post)
    (hgates : ∀ c ∈ escrowCreateRowGates, c.holdsVm env false false) :
    CellEscrowSpec pre p post :=
  intent_to_cellEscrowSpec env pre post p henc ((escrowCreateVm_faithful env).mp hgates)

/-! ## §2 — the WIDE descriptor + spec + the FULL-STATE crown. -/

/-- **`committedEscrowVmDescriptorWide`** — committedEscrow's WIDE RUNNABLE descriptor (= createObligation's,
by dispatch-alias). -/
def committedEscrowVmDescriptorWide : EffectVmDescriptor :=
  escrowFamilyWideDescriptor escrowCreateVmAirName escrowCreateRowGates

/-- **`committedEscrow_runnable_full_sound` — THE MAGNESIUM CROWN for createCommittedEscrow (and
createObligation).** A row satisfying the WIDE RUNNABLE descriptor pins the FULL 17-field post-state:
the per-cell DEBIT (`balLo` − amount, frame frozen, nonce frozen) AND the `escrows` digest ADVANCED by
`step` (the other 7 roots bound through the digest). -/
theorem committedEscrow_runnable_full_sound (p : EscrowParams) (hash : List ℤ → ℤ)
    (preRoots : SysRoots) (step : ℤ)
    (env : VmRowEnv) (pre post : CellState) (postRoots : SysRoots)
    (hrow : IsEscrowCreateRow env)
    (henc : RowEncodesEscrow env pre p post)
    (hAfter : env.loc sysRootsDigestCol = systemRootsDigest hash postRoots)
    (hBefore : env.loc sysRootsDigestColBefore = systemRootsDigest hash preRoots)
    (hStep : env.loc (prmCol ESCROW_STEP_PARAM) = step)
    (hsat : satisfiedVm hash committedEscrowVmDescriptorWide env true true) :
    CellEscrowSpec pre p post
      ∧ systemRootsDigest hash postRoots = systemRootsDigest hash preRoots + step :=
  escrow_family_runnable_full_sound escrowCreateVmAirName escrowCreateRowGates
    escrowCreateRowGates_allGate IsEscrowCreateRow
    (fun env pre post => RowEncodesEscrow env pre p post)
    (fun pre post => CellEscrowSpec pre p post)
    (fun env pre post hrow hdec hgates => committedEscrow_cellFromGates p env pre post hrow hdec hgates)
    hash preRoots step env pre post postRoots hrow henc hAfter hBefore hStep hsat

/-! ## §3 — the WHOLE-STATE anti-ghost. -/

theorem committedEscrow_wide_binds_full_state (p : EscrowParams) (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash) (preRoots : SysRoots) (step : ℤ)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash committedEscrowVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash committedEscrowVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂) :
    absorbedCols e₁ = absorbedCols e₂ ∧ (∀ i : Fin N_SYSTEM_ROOTS, sr₁ i = sr₂ i) :=
  escrowFamily_binds_full_state escrowCreateVmAirName escrowCreateRowGates
    escrowCreateRowGates_allGate IsEscrowCreateRow
    (fun env pre post => RowEncodesEscrow env pre p post)
    (fun pre post => CellEscrowSpec pre p post)
    (fun env pre post hrow hdec hgates => committedEscrow_cellFromGates p env pre post hrow hdec hgates)
    hash hCR preRoots step e₁ e₂ sr₁ sr₂ hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂

/-- **`committedEscrow_wide_rejects_root_tamper` — the NO-MALLEABILITY tooth.** Two WIDE rows publishing
the same `NEW_COMMIT` whose side-table sub-blocks differ at some root index cannot both satisfy. -/
theorem committedEscrow_wide_rejects_root_tamper (p : EscrowParams) (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash) (preRoots : SysRoots) (step : ℤ)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash committedEscrowVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash committedEscrowVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    {i : Fin N_SYSTEM_ROOTS} (htamper : sr₁ i ≠ sr₂ i) : False :=
  htamper ((committedEscrow_wide_binds_full_state p hash hCR preRoots step e₁ e₂ sr₁ sr₂
    hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂).2 i)

/-- **`committedEscrow_wide_rejects_state_tamper` — per-cell-block anti-ghost.** -/
theorem committedEscrow_wide_rejects_state_tamper (p : EscrowParams) (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash) (preRoots : SysRoots) (step : ℤ)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash committedEscrowVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash committedEscrowVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    (htamper : absorbedCols e₁ ≠ absorbedCols e₂) : False :=
  htamper (committedEscrow_wide_binds_full_state p hash hCR preRoots step e₁ e₂ sr₁ sr₂
    hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂).1

/-! ## §4 — NON-VACUITY. -/

def goodPreRoots : SysRoots := emptySystemRoots
def goodPostRoots : SysRoots := fun i => if i = ESCROW_ROOT_INDEX then 1234 else 0
def goodPre : CellState :=
  { balLo := 100, balHi := 0, nonce := 5, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }
def goodPost : CellState :=
  { balLo := 95, balHi := 0, nonce := 5, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }

/-- **NON-VACUITY (witness TRUE).** The committed-escrow full clause is INHABITED for any `hash`: a real
`100 → 95` debit + the genuine digest difference of a MOVED side-table. -/
theorem goodCommitted_realizes (hash : List ℤ → ℤ) :
    EscrowFamilyFullClause (fun pre post => CellEscrowSpec pre ⟨5⟩ post) hash goodPreRoots
      (systemRootsDigest hash goodPostRoots - systemRootsDigest hash goodPreRoots)
      goodPre goodPost goodPostRoots := by
  refine ⟨⟨by norm_num [goodPre, goodPost], rfl, rfl, fun _ => rfl, rfl, rfl⟩, ?_⟩
  ring

theorem goodCommitted_roots_moved : goodPostRoots ESCROW_ROOT_INDEX ≠ goodPreRoots ESCROW_ROOT_INDEX := by
  simp only [goodPostRoots, goodPreRoots, emptySystemRoots, if_pos]
  norm_num

/-- **`committedEscrow_clause_refutable` — the clause is REFUTABLE (witness FALSE).** -/
theorem committedEscrow_clause_refutable (hash : List ℤ → ℤ) (preRoots postRoots : SysRoots) (step : ℤ) :
    ¬ EscrowFamilyFullClause (fun pre post => CellEscrowSpec pre ⟨5⟩ post) hash preRoots step
        goodPre { goodPost with balLo := 999 } postRoots := by
  rintro ⟨⟨hbal, _⟩, _⟩
  simp only [goodPre] at hbal
  norm_num at hbal

/-! ## §5 — layout pins + axiom hygiene. -/

#guard committedEscrowVmDescriptorWide.traceWidth == EFFECT_VM_WIDTH_SYSROOTS
#guard committedEscrowVmDescriptorWide.traceWidth == 188
#guard committedEscrowVmDescriptorWide.hashSites.length == 4
#guard committedEscrowVmDescriptorWide.constraints.length == 13 + 1 + 14 + 4 + 3

#assert_axioms escrowCreateRowGates_allGate
#assert_axioms committedEscrow_cellFromGates
#assert_axioms committedEscrow_runnable_full_sound
#assert_axioms committedEscrow_wide_binds_full_state
#assert_axioms committedEscrow_wide_rejects_root_tamper
#assert_axioms committedEscrow_wide_rejects_state_tamper
#assert_axioms goodCommitted_realizes
#assert_axioms goodCommitted_roots_moved
#assert_axioms committedEscrow_clause_refutable

end Dregg2.Circuit.Emit.EffectVmEmitCreateCommittedEscrowWide

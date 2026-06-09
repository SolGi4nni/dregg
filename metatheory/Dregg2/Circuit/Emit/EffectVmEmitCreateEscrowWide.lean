/-
# Dregg2.Circuit.Emit.EffectVmEmitCreateEscrowWide — the createEscrow RUNNABLE descriptor lifted to
FULL-STATE (the magnesium breadth): the circuit the prover RUNS binds all 17 `RecordKernelState` fields.

`EffectVmEmitCreateEscrow` proved createEscrow's per-cell soundness (`createEscrowVm_faithful` +
`intent_to_cellCreateSpec` ⇒ `CellCreateSpec`: the `balLo` DEBIT by `amount`, the whole frame frozen,
nonce frozen) and bound the `escrows` root into `state_commit` via the RAW `aux_off_sys.SYSTEM_ROOTS_DIGEST`
(= 96) carrier. That carrier is benign but not the clean, generically-liftable home: the generic
full-state crown (`EffectVmFullStateRunnable.runnable_full_sound`) consumes the DEDICATED, non-aliasing
`sysRootsDigestCol` (= 186) carrier + the `wideHashSites` shape + `EFFECT_VM_WIDTH_SYSROOTS`.

This module re-targets createEscrow's escrow-root carrier onto the dedicated `sysRootsDigestCol` (via the
shared `EffectVmEmitEscrowFamilyWide` builder) and lifts it through the generic crown:
`createEscrow_runnable_full_sound` — a satisfying witness of the WIDE RUNNABLE descriptor pins the FULL
17-field declarative post-state (the per-cell debit + frame freeze AND the `escrows` side-table digest
advance, with the OTHER 7 roots bound through the digest). The NO-MALLEABILITY tooth
(`createEscrow_wide_rejects_*`) follows from the generic anti-ghost: tamper ANY field (incl. ANY
side-table root) ⇒ the running descriptor is UNSAT.

## Honesty
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY through the named
`Poseidon2SpongeCR` carrier inside the generic crown's anti-ghost. No `sorry`/`:= True`/`native_decide`.
This module OWNS only itself; every import is read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitEscrowFamilyWide
import Dregg2.Circuit.Emit.EffectVmEmitCreateEscrow

namespace Dregg2.Circuit.Emit.EffectVmEmitCreateEscrowWide

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState absorbedCols)
open Dregg2.Circuit.Emit.EffectVmEmitCreateEscrow
  (createEscrowRowGates createEscrowVmAirName IsCreateEscrowRow RowEncodesCreate CellCreateSpec
   CreateParams intent_to_cellCreateSpec createEscrowVm_faithful gBalLoDebit gNonceFreeze
   goodCreateRow goodCreateRow_realizes_intent)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gBalHi gCapPass gResPass gFieldPass gFieldPassAll)
open Dregg2.Circuit.Emit.EffectVmEmitEscrowFamilyWide
  (escrowFamilyWideDescriptor escrowFamilyWideSpec escrow_family_runnable_full_sound
   escrowFamily_binds_full_state EscrowFamilyFullClause ESCROW_STEP_PARAM ESCROW_ROOT_INDEX)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.SystemRoots (SysRoots systemRootsDigest N_SYSTEM_ROOTS emptySystemRoots)

set_option linter.unusedVariables false

/-! ## §1 — createEscrow's per-row gates are all `.gate`s (the `hAllGates` obligation). -/

/-- `createEscrowRowGates` are all `.gate` constraints (debit + bal_hi/nonce/cap/reserved freeze + 8
fields). Needed by the family builder to project them flag-free off the wide constraint list. -/
theorem createEscrowRowGates_allGate : ∀ g ∈ createEscrowRowGates, ∃ b, g = .gate b := by
  intro g hg
  unfold createEscrowRowGates gFieldPassAll at hg
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_range] at hg
  rcases hg with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
  · exact ⟨gBalLoDebit, rfl⟩
  · exact ⟨gBalHi, rfl⟩
  · exact ⟨gNonceFreeze, rfl⟩
  · exact ⟨gCapPass, rfl⟩
  · exact ⟨gResPass, rfl⟩
  · exact ⟨gFieldPass i, rfl⟩

/-! ## §2 — the per-cell gate-soundness (createEscrow's `CellCreateSpec`, flag-free). -/

/-- **`createEscrow_cellFromGates`** — createEscrow's row gates (flag-free), on a create row decoded by
`RowEncodesCreate`, force `CellCreateSpec`. This is `intent_to_cellCreateSpec ∘ createEscrowVm_faithful`
— the per-cell debit + frame freeze, the body the family lift plugs in. NEITHER reads a hash-site. -/
theorem createEscrow_cellFromGates (p : CreateParams) (env : VmRowEnv) (pre post : CellState)
    (hrow : IsCreateEscrowRow env) (henc : RowEncodesCreate env pre p post)
    (hgates : ∀ c ∈ createEscrowRowGates, c.holdsVm env false false) :
    CellCreateSpec pre p post :=
  intent_to_cellCreateSpec env pre post p henc ((createEscrowVm_faithful env).mp hgates)

/-! ## §3 — the WIDE createEscrow RUNNABLE descriptor + spec + the FULL-STATE crown. -/

/-- **`createEscrowVmDescriptorWide`** — createEscrow's WIDE RUNNABLE descriptor: the existing per-row
debit/freeze gates ++ the dedicated-carrier escrow-root-update gate ++ transition ++ the 7 boundary pins,
`traceWidth := EFFECT_VM_WIDTH_SYSROOTS`, `hashSites := wideHashSites`. -/
def createEscrowVmDescriptorWide : EffectVmDescriptor :=
  escrowFamilyWideDescriptor createEscrowVmAirName createEscrowRowGates

/-- **`createEscrowRunnableSpec p preRoots step`** — the createEscrow `RunnableFullStateSpec`: the WIDE
descriptor, `IsCreateEscrowRow`, `RowEncodesCreate`-decode, and the `EscrowFamilyFullClause` (the per-cell
`CellCreateSpec` DEBIT AND the `escrows` digest advance). THIN — `decodeFull` is the family lift over
`createEscrow_cellFromGates`. -/
def createEscrowRunnableSpec (p : CreateParams) (hash : List ℤ → ℤ) (preRoots : SysRoots) (step : ℤ) :=
  escrowFamilyWideSpec createEscrowVmAirName createEscrowRowGates createEscrowRowGates_allGate
    IsCreateEscrowRow
    (fun env pre post => RowEncodesCreate env pre p post)
    (fun pre post => CellCreateSpec pre p post)
    (fun env pre post hrow hdec hgates => createEscrow_cellFromGates p env pre post hrow hdec hgates)
    hash preRoots step

/-- **`createEscrow_runnable_full_sound` — THE MAGNESIUM CROWN for createEscrow.** A row satisfying the
WIDE RUNNABLE createEscrow descriptor (`satisfiedVm`, first/last active), under the `RowEncodesCreate`
decode + the dedicated digest-carrier/step pins, pins the FULL 17-field declarative post-state: the
per-cell DEBIT (`balLo` − amount, whole frame frozen, nonce frozen) AND the `escrows` side-table digest
ADVANCED by `step` (the other 7 roots bound through the digest). The crypto is discharged ONCE in the
generic crown; here it is the (already-proved) per-cell soundness + the root-update gate. -/
theorem createEscrow_runnable_full_sound (p : CreateParams) (hash : List ℤ → ℤ)
    (preRoots : SysRoots) (step : ℤ)
    (env : VmRowEnv) (pre post : CellState) (postRoots : SysRoots)
    (hrow : IsCreateEscrowRow env)
    (henc : RowEncodesCreate env pre p post)
    (hAfter : env.loc sysRootsDigestCol = systemRootsDigest hash postRoots)
    (hBefore : env.loc sysRootsDigestColBefore = systemRootsDigest hash preRoots)
    (hStep : env.loc (prmCol ESCROW_STEP_PARAM) = step)
    (hsat : satisfiedVm hash createEscrowVmDescriptorWide env true true) :
    CellCreateSpec pre p post
      ∧ systemRootsDigest hash postRoots = systemRootsDigest hash preRoots + step :=
  escrow_family_runnable_full_sound createEscrowVmAirName createEscrowRowGates
    createEscrowRowGates_allGate IsCreateEscrowRow
    (fun env pre post => RowEncodesCreate env pre p post)
    (fun pre post => CellCreateSpec pre p post)
    (fun env pre post hrow hdec hgates => createEscrow_cellFromGates p env pre post hrow hdec hgates)
    hash preRoots step env pre post postRoots hrow henc hAfter hBefore hStep hsat

/-! ## §4 — the WHOLE-STATE anti-ghost (all 17 fields' tamper ⇒ UNSAT on the runnable descriptor). -/

/-- **`createEscrow_wide_binds_full_state`** — two WIDE createEscrow rows publishing the SAME `NEW_COMMIT`
(carriers = `systemRootsDigest` of their post sub-blocks) agree on EVERY absorbed state-block column AND
every side-table root. The whole post-state is bound by the runnable commitment (no malleability). -/
theorem createEscrow_wide_binds_full_state (p : CreateParams) (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash) (preRoots : SysRoots) (step : ℤ)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash createEscrowVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash createEscrowVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂) :
    absorbedCols e₁ = absorbedCols e₂ ∧ (∀ i : Fin N_SYSTEM_ROOTS, sr₁ i = sr₂ i) :=
  escrowFamily_binds_full_state createEscrowVmAirName createEscrowRowGates
    createEscrowRowGates_allGate IsCreateEscrowRow
    (fun env pre post => RowEncodesCreate env pre p post)
    (fun pre post => CellCreateSpec pre p post)
    (fun env pre post hrow hdec hgates => createEscrow_cellFromGates p env pre post hrow hdec hgates)
    hash hCR preRoots step e₁ e₂ sr₁ sr₂ hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂

/-- **`createEscrow_wide_rejects_root_tamper` — the headline NO-MALLEABILITY tooth.** Two WIDE createEscrow
rows publishing the SAME `NEW_COMMIT` (with `systemRootsDigest` carriers) whose side-table sub-blocks
DIFFER at some root index `i` (a dropped escrow, an omitted nullifier, a reordered queue) cannot BOTH
satisfy — the side-table state is bound BY the runnable commitment. -/
theorem createEscrow_wide_rejects_root_tamper (p : CreateParams) (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash) (preRoots : SysRoots) (step : ℤ)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash createEscrowVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash createEscrowVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    {i : Fin N_SYSTEM_ROOTS} (htamper : sr₁ i ≠ sr₂ i) : False :=
  htamper ((createEscrow_wide_binds_full_state p hash hCR preRoots step e₁ e₂ sr₁ sr₂
    hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂).2 i)

/-- **`createEscrow_wide_rejects_state_tamper` — per-cell-block anti-ghost.** Two WIDE createEscrow rows
publishing the same `NEW_COMMIT` whose absorbed state-block columns DIFFER cannot both satisfy. A forged
balance / tampered field / forged cap-root that still claims the published commitment is UNSAT. -/
theorem createEscrow_wide_rejects_state_tamper (p : CreateParams) (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash) (preRoots : SysRoots) (step : ℤ)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash createEscrowVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash createEscrowVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    (htamper : absorbedCols e₁ ≠ absorbedCols e₂) : False :=
  htamper (createEscrow_wide_binds_full_state p hash hCR preRoots step e₁ e₂ sr₁ sr₂
    hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂).1

/-! ## §5 — NON-VACUITY: the full clause is inhabited by a real debit + a real digest advance, and
refutable by a forged post-balance. -/

/-- The empty before-roots reference (escrow store empty before the create). -/
def goodPreRoots : SysRoots := emptySystemRoots

/-- A populated AFTER sub-block (the escrow store now holds a record at the ESCROW root). DISTINCT from
`goodPreRoots` — the side-table genuinely moved. -/
def goodPostRoots : SysRoots := fun i => if i = ESCROW_ROOT_INDEX then 1234 else 0

/-- A real debited pre/post pair: `balLo 100 → 95` (debit 5), the whole frame frozen at 0. -/
def goodCreatePre : CellState :=
  { balLo := 100, balHi := 0, nonce := 5, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }
def goodCreatePost : CellState :=
  { balLo := 95, balHi := 0, nonce := 5, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }

/-- **NON-VACUITY (witness TRUE).** The createEscrow full clause is INHABITED for any `hash`: a real
`100 → 95` debit satisfies `CellCreateSpec`, and the genuine step `systemRootsDigest goodPostRoots −
systemRootsDigest goodPreRoots` (the actual digest difference of a MOVED side-table) satisfies the
side-table conjunct by `ring`. So the `fullClause` is a genuine 17-field predicate, NOT `True`, and the
witness is realizable over the abstract carrier. -/
theorem goodCreate_realizes (hash : List ℤ → ℤ) :
    EscrowFamilyFullClause (fun pre post => CellCreateSpec pre ⟨5⟩ post) hash goodPreRoots
      (systemRootsDigest hash goodPostRoots - systemRootsDigest hash goodPreRoots)
      goodCreatePre goodCreatePost goodPostRoots := by
  refine ⟨⟨by norm_num [goodCreatePre, goodCreatePost], rfl, rfl, fun _ => rfl, rfl, rfl⟩, ?_⟩
  ring

/-- The non-vacuity witness genuinely MOVES the escrow side-table (the post sub-block differs from the
pre at the ESCROW root) — so `goodCreate_realizes` is not a frozen-roots costume. -/
theorem goodCreate_roots_moved : goodPostRoots ESCROW_ROOT_INDEX ≠ goodPreRoots ESCROW_ROOT_INDEX := by
  simp only [goodPostRoots, goodPreRoots, emptySystemRoots, if_pos]
  norm_num

/-- **`createEscrow_clause_refutable` — the clause is REFUTABLE (witness FALSE).** A post-state whose
`balLo` is NOT the debit (`goodCreatePre.balLo = 100`, demanding `95`, but a forged `999`) FAILS the
per-cell conjunct — so the full clause is not vacuously true. -/
theorem createEscrow_clause_refutable (hash : List ℤ → ℤ) (preRoots : SysRoots) (postRoots : SysRoots)
    (step : ℤ) :
    ¬ EscrowFamilyFullClause (fun pre post => CellCreateSpec pre ⟨5⟩ post) hash preRoots step
        goodCreatePre { goodCreatePost with balLo := 999 } postRoots := by
  rintro ⟨⟨hbal, _⟩, _⟩
  simp only [goodCreatePre] at hbal
  norm_num at hbal

/-! ## §6 — layout pins + axiom hygiene. -/

#guard createEscrowVmDescriptorWide.traceWidth == EFFECT_VM_WIDTH_SYSROOTS
#guard createEscrowVmDescriptorWide.traceWidth == 188
#guard createEscrowVmDescriptorWide.hashSites.length == 4
-- 13 createEscrow row gates + 1 root-update + 14 transition + 4 first + 3 last.
#guard createEscrowVmDescriptorWide.constraints.length == 13 + 1 + 14 + 4 + 3

#assert_axioms createEscrowRowGates_allGate
#assert_axioms createEscrow_cellFromGates
#assert_axioms createEscrow_runnable_full_sound
#assert_axioms createEscrow_wide_binds_full_state
#assert_axioms createEscrow_wide_rejects_root_tamper
#assert_axioms createEscrow_wide_rejects_state_tamper
#assert_axioms goodCreate_realizes
#assert_axioms goodCreate_roots_moved
#assert_axioms createEscrow_clause_refutable

end Dregg2.Circuit.Emit.EffectVmEmitCreateEscrowWide

/-
# Dregg2.Circuit.Emit.EffectVmEmitCreateSealPair — the createSealPair (mint a sealer/unsealer keypair)
effect's concrete EffectVM circuit, EMITTED through the SAME `EffectVmEmit` IR as transfer.

Universe A (`Inst/createSealPairA.lean`, `Spec/sealpaircreation.lean`) carries the FULL-state soundness
`createSealPair_iff_spec ⇒ CreateSealPairSpec`: a committed pair-creation performs a DOUBLE c-list
grant — the sealer cap `sealerCap pid` to `sealerHolder` AND the unsealer cap `unsealerCap pid` to
`unsealerHolder` (`caps := createSealPairCaps …`) — advances the chained `log`, and is otherwise
TOTALLY NEUTRAL — balance-neutral (`createSealPair_spec_balance_neutral`: `bal`/accounts/sealedBoxes
unchanged) and FREEZES the other kernel fields. Guard: `actor` holds authority over `sealerHolder`.

## THE KEY STRUCTURAL FACT (and the honest IR boundary)

A createSealPair touches NEITHER the per-asset `bal` ledger NOR any per-cell state-block column — it
only GRANTS two caps into the `caps` SIDE-TABLE (a structure the EffectVM 14-column state block has NO
column for, absorbed by NO GROUP-4 hash-site). So, projected onto ONE EffectVM cell's state block, a
createSealPair is a PURE FREEZE: every state-block column UNCHANGED, and the published `state_commit`
is the genuine digest of the FROZEN after-state.

What the IR DOES support is exactly this FREEZE + the commitment binding of the frozen block — the
conservation / balance-neutrality tooth (a row claiming a createSealPair but mutating any cell is
UNSAT).

## THE IR-EXTENSION FLAG (the double cap-grant — the LOAD-BEARING leg, out-of-IR)

The actual effect — `caps := grant (grant caps sealerHolder (sealerCap pid)) unsealerHolder
(unsealerCap pid)` — is a DOUBLE GRANT of two distinct CAPABILITIES (a real keypair: `[grant]` vs
`[reply]` rights) into the cap-table side-structure. The EffectVM 14-column block has NO cap-table-root
column, and the GROUP-4 hash-sites absorb none of `caps`. So the per-row circuit CANNOT bind, or even
witness, either granted cap or its holder.

  ⇒ **needs IR extension: a caps-table-root column in the EffectVM state block absorbed by a new
     hash-site, plus param columns carrying `pid`/`sealerHolder`/`unsealerHolder`, so the double grant
     is bound into the published `state_commit`.** The authority-over-`sealerHolder` guard is likewise
     out-of-row. Reported, not papered.

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY as the named
`Poseidon2SpongeCR` hypothesis. No `sorry`, no `:= True`, no `native_decide`. Imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.sealpaircreation

namespace Dregg2.Circuit.Emit.EffectVmEmitCreateSealPair

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA eSub gBalHi gCapPass gResPass gFieldPass gFieldPassAll
   transitionAll boundaryFirstPins boundaryLastPins
   transferHashSites transferHash_binds boundaryLast_pins)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (CellState absorbedCols commitOf commit_eq_commitOf absorbed_determined_by_commit)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.CircuitEmit (EmittedExpr)

set_option linter.unusedVariables false

/-! ## §0 — The createSealPair selector. -/

/-- The create-seal-pair selector column index. -/
def SEL_CREATE_SEAL_PAIR : Nat := 8

/-- The pair-creation row: `s_create_seal_pair = 1`, `s_noop = 0`. -/
def IsCreateSealPairRow (env : VmRowEnv) : Prop :=
  env.loc SEL_CREATE_SEAL_PAIR = 1 ∧ env.loc sel.NOOP = 0

/-! ## §1 — The per-row gate bodies (WHOLE state-block FREEZE). -/

/-- Balance-lo FREEZE body: `new_bal_lo − old_bal_lo` (balance-neutral — minting a keypair moves no
value). -/
def gBalLoFreeze : EmittedExpr := eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)

/-- Nonce-FREEZE body: `new_nonce − old_nonce`. -/
def gNonceFreeze : EmittedExpr := eSub (eSA state.NONCE) (eSB state.NONCE)

/-! ## §2 — The emitted descriptor. -/

/-- The create-seal-pair AIR identity. -/
def createSealPairVmAirName : String := "dregg-effectvm-createsealpair-v1"

/-- The per-row gates: WHOLE state block frozen. -/
def createSealPairRowGates : List VmConstraint :=
  [ .gate gBalLoFreeze, .gate gBalHi, .gate gNonceFreeze
  , .gate gCapPass, .gate gResPass ] ++ gFieldPassAll

/-- **`createSealPairVmDescriptor`** — the createSealPair effect's concrete EffectVM circuit: the
per-row WHOLE-block freeze gates ++ transition continuity ++ the 7 boundary PI pins, with the 4 ordered
GROUP-4 hash sites (REUSED — binding the frozen block) and the 2 balance-limb range checks. -/
def createSealPairVmDescriptor : EffectVmDescriptor :=
  { name := createSealPairVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := createSealPairRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §3 — The ROW INTENT: the WHOLE state block frozen. -/

/-- **`CreateSealPairRowIntent env`** — the intended createSealPair move on the row `env.loc`: every
state-block column UNCHANGED. The double cap-grant + authority guard are out-of-row (the §IR flags). -/
def CreateSealPairRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-! ## §4 — FAITHFULNESS: the emitted per-row gates ⟺ the freeze intent. -/

/-- **`createSealPairVm_faithful`.** On a pair-creation row, the emitted descriptor's per-row gates all
hold IFF `CreateSealPairRowIntent` holds — the gates pin EXACTLY the whole-block freeze. -/
theorem createSealPairVm_faithful (env : VmRowEnv) :
    (∀ c ∈ createSealPairRowGates, c.holdsVm env false false) ↔ CreateSealPairRowIntent env := by
  unfold createSealPairRowGates gFieldPassAll CreateSealPairRowIntent
  constructor
  · intro h
    have hLo := h (.gate gBalLoFreeze) (by simp)
    have hHi := h (.gate gBalHi) (by simp)
    have hNon := h (.gate gNonceFreeze) (by simp)
    have hCap := h (.gate gCapPass) (by simp)
    have hRes := h (.gate gResPass) (by simp)
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (.gate (gFieldPass i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gBalLoFreeze, gBalHi, gNonceFreeze, gCapPass, gResPass,
      eSA, eSB, eSub, EmittedExpr.eval] at hLo hHi hNon hCap hRes
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · linarith [hLo]
    · linarith [hHi]
    · linarith [hNon]
    · linarith [hCap]
    · linarith [hRes]
    · intro i hi
      have := hFld i hi
      simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval] at this
      linarith
  · rintro ⟨hLo, hHi, hNon, hCap, hRes, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
    · simp only [VmConstraint.holdsVm, gBalLoFreeze, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hLo]; ring
    · simp only [VmConstraint.holdsVm, gBalHi, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hHi]; ring
    · simp only [VmConstraint.holdsVm, gNonceFreeze, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hNon]; ring
    · simp only [VmConstraint.holdsVm, gCapPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hCap]; ring
    · simp only [VmConstraint.holdsVm, gResPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hRes]; ring
    · simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hFld i hi]; ring

/-! ## §5 — ANTI-GHOST: a row that MUTATES any state-block cell on a pair-creation is rejected. -/

/-- **Anti-ghost (general).** A pair-creation row whose state block is NOT frozen does NOT satisfy the
per-row gates — the conservation tooth. -/
theorem createSealPairVm_rejects_wrong_output (env : VmRowEnv)
    (hwrong : ¬ CreateSealPairRowIntent env) :
    ¬ (∀ c ∈ createSealPairRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((createSealPairVm_faithful env).mp h)

/-- **Anti-ghost (balance tamper).** A pair-creation row whose post-`bal_lo` is NOT the pre-`bal_lo`
(value forged on a balance-neutral effect) has no satisfying gate set — `gBalLoFreeze` rejects it. -/
theorem createSealPairVm_rejects_balance_mint (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO) ≠ env.loc (sbCol state.BALANCE_LO)) :
    ¬ (VmConstraint.gate gBalLoFreeze).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoFreeze, eSA, eSB, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith [h]

/-! ## §6 — The structured per-cell spec (REUSING `CellState`): the FROZEN cell. -/

/-- `RowEncodesPair env pre post` ties the row's state-block columns to a `(pre, post)` cell transition
(no params — pair-creation carries pid/holders off-block). -/
def RowEncodesPair (env : VmRowEnv) (pre post : CellState) : Prop :=
  env.loc (sbCol state.BALANCE_LO) = pre.balLo
  ∧ env.loc (sbCol state.BALANCE_HI) = pre.balHi
  ∧ env.loc (sbCol state.NONCE) = pre.nonce
  ∧ (∀ i : Fin 8, env.loc (sbCol (state.FIELD_BASE + i.val)) = pre.fields i)
  ∧ env.loc (sbCol state.CAP_ROOT) = pre.capRoot
  ∧ env.loc (sbCol state.RESERVED) = pre.reserved
  ∧ env.loc (sbCol state.STATE_COMMIT) = pre.commit
  ∧ env.loc (saCol state.BALANCE_LO) = post.balLo
  ∧ env.loc (saCol state.BALANCE_HI) = post.balHi
  ∧ env.loc (saCol state.NONCE) = post.nonce
  ∧ (∀ i : Fin 8, env.loc (saCol (state.FIELD_BASE + i.val)) = post.fields i)
  ∧ env.loc (saCol state.CAP_ROOT) = post.capRoot
  ∧ env.loc (saCol state.RESERVED) = post.reserved
  ∧ env.loc (saCol state.STATE_COMMIT) = post.commit
  ∧ env.pub pi.OLD_COMMIT = pre.commit
  ∧ env.pub pi.NEW_COMMIT = post.commit

/-- **`CellPairSpec pre post`** — the per-cell FULL-state pair-creation spec: the WHOLE cell state is
FROZEN. This is the EffectVM-row projection of `CreateSealPairSpec`'s balance-neutrality + per-cell
frame freeze (the double cap-grant is off-block — the §IR flag). -/
def CellPairSpec (pre post : CellState) : Prop :=
  post.balLo = pre.balLo
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

/-- Decode lemma: under `RowEncodesPair`, `CreateSealPairRowIntent` IS the structured `CellPairSpec`. -/
theorem intent_to_cellPairSpec (env : VmRowEnv) (pre post : CellState)
    (henc : RowEncodesPair env pre post) (hint : CreateSealPairRowIntent env) :
    CellPairSpec pre post := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hsbC,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes, hsaC, hOld, hNew⟩ := henc
  obtain ⟨hbal, hbhi, hnon, hcap, hres, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hsaLo, ← hsbLo]; exact hbal
  · rw [← hsaHi, ← hsbHi]; exact hbhi
  · rw [← hsaN, ← hsbN]; exact hnon
  · intro i
    have := hfld i.val i.isLt
    rw [← hsaF i, ← hsbF i]; exact this
  · rw [← hsaCap, ← hsbCap]; exact hcap
  · rw [← hsaRes, ← hsbRes]; exact hres

/-! ## §7 — The full descriptor soundness + the commitment binding. -/

/-- **`createSealPairDescriptor_full_sound`** — satisfying the WHOLE runnable descriptor, under
`RowEncodesPair`, forces the structured per-cell FREEZE `CellPairSpec` AND publishes the post-commit as
`PI[NEW_COMMIT]`. -/
theorem createSealPairDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState)
    (henc : RowEncodesPair env pre post)
    (hsat : satisfiedVm hash createSealPairVmDescriptor env true true) :
    CellPairSpec pre post ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, _⟩ := hsat
  have hgates' : ∀ c ∈ createSealPairRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ createSealPairVmDescriptor.constraints := by
      unfold createSealPairVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl hc))
    have := hcs c hmem
    unfold createSealPairRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using this
  have hint := (createSealPairVm_faithful env).mp hgates'
  refine ⟨intent_to_cellPairSpec env pre post henc hint, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ createSealPairVmDescriptor.constraints := by
      unfold createSealPairVmDescriptor
      simp only [List.mem_append]
      exact Or.inr hc
    have hh := hcs c hmem
    unfold boundaryLastPins at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;>
      · simp only [VmConstraint.holdsVm] at hh ⊢
        exact hh
  have hpin := (boundaryLast_pins env hlast).1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hsaC, _, _⟩ := henc
  rw [← hsaC]; exact hpin

/-! ## §8 — The anti-ghost commitment tooth (REUSED; hash sites identical to transfer's). -/

/-- **`createSealPairDescriptor_commit_binds_state`** — two descriptor-satisfying pair-creation rows
publishing the SAME `NEW_COMMIT` have identical absorbed state-block columns. So a prover cannot keep
`NEW_COMMIT` while tampering any absorbed cell of the (frozen) post-state. -/
theorem createSealPairDescriptor_commit_binds_state (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hsat₁ : satisfiedVm hash createSealPairVmDescriptor e₁ true true)
    (hsat₂ : satisfiedVm hash createSealPairVmDescriptor e₂ true true)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT) :
    absorbedCols e₁ = absorbedCols e₂ := by
  have hs₁ : siteHoldsAll hash e₁ transferHashSites := hsat₁.2
  have hs₂ : siteHoldsAll hash e₂ transferHashSites := hsat₂.2
  have hc : ∀ (e : VmRowEnv), satisfiedVm hash createSealPairVmDescriptor e true true →
      e.loc (saCol state.STATE_COMMIT) = e.pub pi.NEW_COMMIT := by
    intro e hsat
    obtain ⟨hcs, _⟩ := hsat
    have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm e false true := by
      intro c hc
      have hmem : c ∈ createSealPairVmDescriptor.constraints := by
        unfold createSealPairVmDescriptor
        simp only [List.mem_append]
        exact Or.inr hc
      have hh := hcs c hmem
      unfold boundaryLastPins at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;>
        · simp only [VmConstraint.holdsVm] at hh ⊢
          exact hh
    exact (boundaryLast_pins e hlast).1
  have hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT) := by
    rw [hc e₁ hsat₁, hc e₂ hsat₂, hpub]
  exact absorbed_determined_by_commit hash hCR e₁ e₂ hs₁ hs₂ hcommit

/-! ## §9 — CONNECTOR to universe-A: `CellPairSpec` IS `CreateSealPairSpec`'s per-cell frame image.

`createSealPair_iff_spec ⇒ CreateSealPairSpec` carries balance-neutrality (`bal' = bal`). We project
ONE cell into the keystone `CellState` and prove the projection of ANY cell satisfies `CellPairSpec`
EXACTLY (all FROZEN). The double cap-grant is the §IR-extension flag, reported below as out-of-row. -/

open Dregg2.Exec (RecChainedState RecordKernelState CellId AssetId)
open Dregg2.Circuit.Spec.SealPairCreation
  (CreateSealPairSpec createSealPair_iff_spec createSealPair_spec_balance_neutral
   createSealPair_spec_grants_keypair)

/-- Project the `(c, asset)` per-asset ledger entry into the keystone `CellState` (the conserved
`balLo` limb; the other EffectVM limbs are `0`, frozen). -/
def cellProjPair (bal : CellId → AssetId → ℤ) (c : CellId) (asset : AssetId) : CellState where
  balLo    := bal c asset
  balHi    := 0
  nonce    := 0
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-- **`unify_pair_freeze`** — ANY cell's projected `(c, asset)` ledger entry, across a committed
`CreateSealPairSpec` post-state, satisfies the keystone's `CellPairSpec` EXACTLY: `balLo` FROZEN
(`bal' = bal`, balance-neutral); the rest frozen. So `CellPairSpec` IS `CreateSealPairSpec`'s per-cell
frame image — NOT a fourth spec. -/
theorem unify_pair_freeze (s s' : RecChainedState) (pid : Nat)
    (actor sealerHolder unsealerHolder c : CellId) (asset : AssetId)
    (hspec : CreateSealPairSpec s pid actor sealerHolder unsealerHolder s') :
    CellPairSpec (cellProjPair s.kernel.bal c asset) (cellProjPair s'.kernel.bal c asset) := by
  refine ⟨?_, rfl, rfl, fun _ => rfl, rfl, rfl⟩
  show s'.kernel.bal c asset = s.kernel.bal c asset
  -- CreateSealPairSpec: guard ∧ caps ∧ log ∧ accounts ∧ cell ∧ escrows ∧ nullifiers ∧ revoked ∧
  --                     commitments ∧ bal ∧ … — `bal` is the 10th conjunct.
  obtain ⟨_, _, _, _, _, _, _, _, _, hbal, _⟩ := hspec
  rw [hbal]

/-! ## §10 — THE per-cell circuit⟺executor AGREEMENT (the payoff). -/

/-- **`descriptor_agrees_with_executor_pair`** — a satisfying run of the runnable descriptor encoding
ANY cell of a committed pair-creation agrees with the executor's per-cell post-state: the descriptor's
pinned (frozen) post-state equals the executor's frozen cell on every state-block column. The double
cap-grant is out-of-IR (reported as the §IR flag). -/
theorem descriptor_agrees_with_executor_pair
    (hash : List ℤ → ℤ) (env : VmRowEnv)
    (s s' : RecChainedState) (pid : Nat) (actor sealerHolder unsealerHolder c : CellId)
    (asset : AssetId) (pre post : CellState)
    (hpre : pre = cellProjPair s.kernel.bal c asset)
    (henc : RowEncodesPair env pre post)
    (hsat : satisfiedVm hash createSealPairVmDescriptor env true true)
    (hspec : CreateSealPairSpec s pid actor sealerHolder unsealerHolder s') :
    post.balLo = (cellProjPair s'.kernel.bal c asset).balLo
    ∧ post.balHi = (cellProjPair s'.kernel.bal c asset).balHi
    ∧ (∀ i, post.fields i = (cellProjPair s'.kernel.bal c asset).fields i)
    ∧ post.capRoot = (cellProjPair s'.kernel.bal c asset).capRoot
    ∧ post.reserved = (cellProjPair s'.kernel.bal c asset).reserved := by
  obtain ⟨hcirc, _⟩ := createSealPairDescriptor_full_sound hash env pre post henc hsat
  obtain ⟨hcLo, hcHi, _, hcF, hcCap, hcRes⟩ := hcirc
  obtain ⟨heLo, heHi, _, heF, heCap, heRes⟩ :=
    unify_pair_freeze s s' pid actor sealerHolder unsealerHolder c asset hspec
  subst hpre
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hcLo, heLo]
  · rw [hcHi, heHi]
  · intro i; rw [hcF i, heF i]
  · rw [hcCap, heCap]
  · rw [hcRes, heRes]

/-! ## §11 — THE DOUBLE CAP-GRANT leg the per-row circuit does NOT enforce (honest, LOAD-BEARING). -/

/-- **`pair_keypair_grant_is_out_of_row` — the honest finding (LOAD-BEARING leg out-of-IR).** A
committed pair-creation over DISTINCT holders GRANTS the sealer cap to `sealerHolder` AND the unsealer
cap to `unsealerHolder` (a real keypair: two GENUINELY DISTINCT held caps —
`createSealPair_spec_grants_keypair`). This double cap-grant — the ACTUAL effect — is a universe-A
property over the `caps` side-table, NOT bound by any per-row gate or hash-site of
`createSealPairVmDescriptor` (whose hash-sites absorb only the 13 frozen state-block columns, none of
`caps`). So the runnable descriptor does NOT bind either grant into `state_commit`: the §IR-extension
flag, surfaced as a theorem. -/
theorem pair_keypair_grant_is_out_of_row (s s' : RecChainedState) (pid : Nat)
    (actor sealerHolder unsealerHolder : CellId)
    (hne : sealerHolder ≠ unsealerHolder)
    (h : Dregg2.Exec.TurnExecutorFull.execFullA s
        (.createSealPairA pid actor sealerHolder unsealerHolder) = some s') :
    Dregg2.Exec.TurnExecutorFull.sealerCap pid ∈ s'.kernel.caps sealerHolder
    ∧ Dregg2.Exec.TurnExecutorFull.unsealerCap pid ∈ s'.kernel.caps unsealerHolder
    ∧ Dregg2.Exec.TurnExecutorFull.sealerCap pid ≠ Dregg2.Exec.TurnExecutorFull.unsealerCap pid := by
  obtain ⟨hms, hmu, _, _, hdne⟩ :=
    createSealPair_spec_grants_keypair s pid actor sealerHolder unsealerHolder s' hne h
  exact ⟨hms, hmu, hdne⟩

/-! ## §12 — NON-VACUITY: a concrete frozen pair-creation row realizes the intent; a minting one
rejected. -/

/-- A concrete pair-creation row: every state-block column frozen (bal_lo 100 → 100, nonce 5 → 5,
frame 0). -/
def goodPairRow : VmRowEnv where
  loc := fun v =>
    if v = SEL_CREATE_SEAL_PAIR then 1
    else if v = sbCol state.BALANCE_LO then 100
    else if v = saCol state.BALANCE_LO then 100
    else if v = sbCol state.NONCE then 5
    else if v = saCol state.NONCE then 5
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- **NON-VACUITY (witness TRUE).** `goodPairRow` REALIZES the pair-creation freeze intent. -/
theorem goodPairRow_realizes_intent : CreateSealPairRowIntent goodPairRow := by
  unfold CreateSealPairRowIntent goodPairRow
  simp only [sbCol, saCol, SEL_CREATE_SEAL_PAIR, STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE,
    NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.BALANCE_HI, state.NONCE,
    state.CAP_ROOT, state.RESERVED, state.FIELD_BASE]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · intro i hi
    have e1 : (76 + (3 + i) = 8) = False := by simp; omega
    have e2 : (76 + (3 + i) = 54) = False := by simp; omega
    have e3 : (76 + (3 + i) = 76) = False := by simp
    have e4 : (76 + (3 + i) = 56) = False := by simp; omega
    have e5 : (76 + (3 + i) = 78) = False := by simp; omega
    have f1 : (54 + (3 + i) = 8) = False := by simp; omega
    have f2 : (54 + (3 + i) = 54) = False := by simp
    have f3 : (54 + (3 + i) = 76) = False := by simp; omega
    have f4 : (54 + (3 + i) = 56) = False := by simp; omega
    have f5 : (54 + (3 + i) = 78) = False := by simp; omega
    simp only [e1, e2, e3, e4, e5, f1, f2, f3, f4, f5, if_false]

/-- A FORGED pair-creation row: `goodPairRow` with the post-`bal_lo` minted to `999`. -/
def badPairRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 999 else goodPairRow.loc v
  nxt := goodPairRow.nxt
  pub := goodPairRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badPairRow`'s post-`bal_lo` is NOT frozen
(forged mint), so `gBalLoFreeze` REJECTS it — a concrete UNSAT (conservation has teeth). -/
theorem badPairRow_rejected : ¬ (VmConstraint.gate gBalLoFreeze).holdsVm badPairRow false false := by
  apply createSealPairVm_rejects_balance_mint
  simp only [badPairRow, goodPairRow, sbCol, saCol, SEL_CREATE_SEAL_PAIR, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
    state.NONCE]
  norm_num

/-! ## §13 — Axiom-hygiene pins. -/

#guard createSealPairVmDescriptor.constraints.length == 13 + 14 + 4 + 3
#guard createSealPairVmDescriptor.hashSites.length == 4
#guard createSealPairVmDescriptor.traceWidth == 186

#assert_axioms createSealPairVm_faithful
#assert_axioms createSealPairVm_rejects_wrong_output
#assert_axioms createSealPairVm_rejects_balance_mint
#assert_axioms intent_to_cellPairSpec
#assert_axioms createSealPairDescriptor_full_sound
#assert_axioms createSealPairDescriptor_commit_binds_state
#assert_axioms unify_pair_freeze
#assert_axioms descriptor_agrees_with_executor_pair
#assert_axioms pair_keypair_grant_is_out_of_row
#assert_axioms goodPairRow_realizes_intent
#assert_axioms badPairRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitCreateSealPair

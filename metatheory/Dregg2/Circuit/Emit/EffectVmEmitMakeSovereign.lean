/-
# Dregg2.Circuit.Emit.EffectVmEmitMakeSovereign — the `makeSovereign` effect's EffectVM-row circuit,
  EMITTED.

`makeSovereign` is SPECIAL (the mandate work flagged it): a FULL record-REBIND of the target cell. It
DROPS the target's entire readable record and installs a COMMITMENT-ONLY record
`[(commitmentField, .dig (stateCommitment (base target)))]` — the cell's prior state collapses behind a
single sovereign commitment. Its FULL universe-A soundness is
`Inst.MakeSovereignA.makeSovereignA_full_sound ⇒ MakeSovereignSpec` (the EffectSpec layer; all 17
kernel fields + log, `cell` the ONE touched component rebound via `sovereignRebind`, every other field
frozen).

## What the EffectVM row CAN pin (the genuine economic consequence of the rebind)

Because the readable record is DROPPED behind a commitment, the target cell's READABLE `balance` field
is GONE — so `balOf (sovereignRebind base target target) = 0` (the commitment-only record carries no
`balance` field). The EffectVM economic block of the TARGET cell therefore becomes the ZERO block
post-rebind. The row pins:

  * the post economic block is the all-zero block (the readable balance/frame are dropped);
  * that zero block is bound into the published `state_commit` under Poseidon2 CR (the anti-ghost
    tooth — but see the boundary: this is the EffectVM Poseidon2 digest, NOT the universe-A
    `stateCommitment` the rebind actually installs).

## What the EffectVM row CANNOT enforce (the boundary — the WHOLE point of the rebind)

`makeSovereign` REPLACES the dropped state with `stateCommitment (base target)` — the universe-A
state-commitment of the WHOLE pre-record. The EffectVM `state_commit` column is a DIFFERENT commitment
function (the Poseidon2 H4-of-H4 of the after-block), so the row's commitment does NOT witness that the
PRE-record was committed under `stateCommitment`. Concretely:

  * the INSTALL of the `commitmentField := stateCommitment(pre)` record — the universe-A commitment of
    the dropped pre-state — is OFF-ROW (the EffectVM block has no column carrying `stateCommitment`);
  * the self-targeted receipt; the self-authority guard.

So the row witnesses that the readable balance was ZEROED by the rebind, but NOT that the dropped state
was sovereign-committed. The rebind SOUNDNESS lives ONLY in `makeSovereignA_full_sound`.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR named hypothesis only. No
`sorry`/`:= True`/`native_decide`. Read-only imports.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.sovereigncommitment

namespace Dregg2.Circuit.Emit.EffectVmEmitMakeSovereign

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (eSA site0 site1 site2)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState RowEncodes)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (sovereignRebind commitmentField stateCommitment)
open Dregg2.Circuit.Spec.SovereignCommitment

set_option linter.unusedVariables false

/-! ## §0 — the `makeSovereign` selector column (local). -/

/-- The `makeSovereign` selector column index. -/
def SEL_MAKESOVEREIGN : Nat := 6

/-! ## §1 — the DROPPED-TO-ZERO per-row gates (the target's readable economic block is zeroed). -/

/-- The drop-to-zero gate for state-block column `off`: `state_after[off] = 0`. -/
def gZero (off : Nat) : VmConstraint := .gate (eSA off)

/-- The 13 drop-to-zero gates (every economic-data column of the rebound block). -/
def makeSovereignRowGates : List VmConstraint :=
  [ gZero state.BALANCE_LO, gZero state.BALANCE_HI, gZero state.NONCE
  , gZero state.CAP_ROOT, gZero state.RESERVED ]
  ++ (List.range 8).map (fun i => gZero (state.FIELD_BASE + i))

/-! ## §2 — the GROUP-4 state-commitment hash sites (reused). -/

def makeSovereignHashSites : List VmHashSite := EffectVmEmitTransfer.transferHashSites

/-! ## §3 — the emitted descriptor. -/

def makeSovereignVmAirName : String := "dregg-effectvm-makesovereign-v1"

/-- **`makeSovereignVmDescriptor`** — the `makeSovereign` EffectVM-row circuit: the 13 drop-to-zero
gates (the rebind drops the readable economic block) + the 4 ordered GROUP-4 hash sites binding the
zero block into `state_commit`. -/
def makeSovereignVmDescriptor : EffectVmDescriptor :=
  { name := makeSovereignVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := makeSovereignRowGates
  , hashSites := makeSovereignHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §4 — the DROPPED-BLOCK row intent. -/

/-- **`DroppedBlockIntent env`** — the row's post-block is the all-zero economic block (the readable
record is dropped behind the sovereign commitment). The EffectVM-row projection of the rebind's
balance-drop. -/
def DroppedBlockIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO) = 0
  ∧ env.loc (saCol state.BALANCE_HI) = 0
  ∧ env.loc (saCol state.NONCE) = 0
  ∧ env.loc (saCol state.CAP_ROOT) = 0
  ∧ env.loc (saCol state.RESERVED) = 0
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = 0)

/-! ## §5 — FAITHFULNESS. -/

theorem makeSovereignVm_faithful (env : VmRowEnv) :
    (∀ c ∈ makeSovereignRowGates, c.holdsVm env false false) ↔ DroppedBlockIntent env := by
  unfold makeSovereignRowGates DroppedBlockIntent
  constructor
  · intro h
    have hLo := h (gZero state.BALANCE_LO) (by simp [gZero])
    have hHi := h (gZero state.BALANCE_HI) (by simp [gZero])
    have hN  := h (gZero state.NONCE) (by simp [gZero])
    have hCap := h (gZero state.CAP_ROOT) (by simp [gZero])
    have hRes := h (gZero state.RESERVED) (by simp [gZero])
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (gZero (state.FIELD_BASE + i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [gZero, VmConstraint.holdsVm, eSA, EmittedExpr.eval] at hLo hHi hN hCap hRes
    refine ⟨hLo, hHi, hN, hCap, hRes, ?_⟩
    intro i hi
    have := hFld i hi
    simp only [gZero, VmConstraint.holdsVm, eSA, EmittedExpr.eval] at this
    exact this
  · rintro ⟨hLo, hHi, hN, hCap, hRes, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simp only [gZero, VmConstraint.holdsVm, eSA, EmittedExpr.eval]
    · exact hLo
    · exact hHi
    · exact hN
    · exact hCap
    · exact hRes
    · exact hFld i hi

/-! ## §6 — ANTI-GHOST. -/

theorem makeSovereignVm_rejects_nonzero (env : VmRowEnv) (hwrong : ¬ DroppedBlockIntent env) :
    ¬ (∀ c ∈ makeSovereignRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((makeSovereignVm_faithful env).mp h)

/-- **Anti-ghost (readable balance survived).** A row whose post-`bal_lo` is non-zero fails the
drop-to-zero gate — a sovereign rebind cannot leave the readable balance behind the commitment. -/
theorem makeSovereignVm_rejects_surviving_balance (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO) ≠ 0) :
    ¬ (gZero state.BALANCE_LO).holdsVm env false false := by
  simp only [gZero, VmConstraint.holdsVm, eSA, EmittedExpr.eval]
  exact hwrong

/-! ## §7 — the commitment binding (inherited from the keystone). -/

open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (absorbedCols absorbed_determined_by_commit)

theorem makeSovereignVm_commit_binds_block (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ makeSovereignHashSites)
    (hs₂ : siteHoldsAll hash e₂ makeSovereignHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    absorbedCols e₁ = absorbedCols e₂ :=
  absorbed_determined_by_commit hash hCR e₁ e₂ hs₁ hs₂ hcommit

/-! ## §8 — the dropped record carries NO readable balance (the overlap with the executor).

The rebound cell IS the commitment-only record `[(commitmentField, .dig (stateCommitment(base)))]`,
which has NO `balance` field — so `balOf = 0`. We prove this from `sovereignRebindMap_correct`. -/

/-- **`sovereignRebind_balOf_zero` — the rebound cell carries `balance == 0`.** The target's rebound
record is commitment-only (`commitmentField ≠ balanceField`), so its `balOf` read fails closed to `0`:
the readable balance is dropped behind the commitment. -/
theorem sovereignRebind_balOf_zero (base : CellId → Value) (target : CellId) :
    balOf (sovereignRebind base target target) = 0 := by
  rw [(sovereignRebindMap_correct base target).1]
  -- balOf (.record [(commitmentField, .dig _)]) : the `balance` field is absent ⇒ 0
  rfl

/-! ## §9 — CONNECTOR to universe-A `MakeSovereignSpec` via `cellProj`. -/

/-- Read cell `c`'s economic block out of the real record-kernel state. -/
def cellProj (k : RecordKernelState) (c : CellId) : CellState where
  balLo    := balOf (k.cell c)
  balHi    := 0
  nonce    := 0
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-- **`makeSovereign_target_dropped` — the OVERLAP, from the executor.** A committed `makeSovereign`
drops the target cell's readable economic block: the projected after-block of `cell` is the all-zero
economic block (the readable balance is dropped behind the sovereign commitment). So
`DroppedBlockIntent` is the executor's effect on the target's economic block. -/
theorem makeSovereign_target_dropped (s s' : RecChainedState) (actor cell : CellId)
    (hspec : MakeSovereignSpec s actor cell s') :
    (cellProj s'.kernel cell).balLo = 0
    ∧ (cellProj s'.kernel cell).balHi = 0
    ∧ (cellProj s'.kernel cell).nonce = 0
    ∧ (cellProj s'.kernel cell).capRoot = 0
    ∧ (cellProj s'.kernel cell).reserved = 0
    ∧ (∀ i, (cellProj s'.kernel cell).fields i = 0) := by
  -- MakeSovereignSpec: guard, cell (= sovereignRebind), log, frame...
  obtain ⟨_, hcellmap, _⟩ := hspec
  refine ⟨?_, rfl, rfl, rfl, rfl, fun _ => rfl⟩
  show balOf (s'.kernel.cell cell) = 0
  rw [hcellmap]
  exact sovereignRebind_balOf_zero s.kernel.cell cell

/-- **`makeSovereign_row_matches_executor` — the CONNECTOR.** If the row's after-block decodes, the
gates hold, and the executor commits `MakeSovereignSpec`, the row's pinned post-block equals the
executor's dropped target block (all zero). -/
theorem makeSovereign_row_matches_executor (env : VmRowEnv) (pre post : CellState)
    (p : EffectVmEmitTransferSound.TransferParams)
    (henc : RowEncodes env pre p post)
    (hgates : ∀ c ∈ makeSovereignRowGates, c.holdsVm env false false)
    (s s' : RecChainedState) (actor cell : CellId)
    (hspec : MakeSovereignSpec s actor cell s') :
    post.balLo = (cellProj s'.kernel cell).balLo
    ∧ post.balHi = (cellProj s'.kernel cell).balHi
    ∧ post.capRoot = (cellProj s'.kernel cell).capRoot
    ∧ post.reserved = (cellProj s'.kernel cell).reserved
    ∧ (∀ i, post.fields i = (cellProj s'.kernel cell).fields i) := by
  obtain ⟨hLo, hHi, hN, hCap, hRes, hFld⟩ := (makeSovereignVm_faithful env).mp hgates
  obtain ⟨eLo, eHi, eN, eCap, eRes, eFld⟩ := makeSovereign_target_dropped s s' actor cell hspec
  obtain ⟨_, _, _, _, _, _, _, _, _, hsaLo, hsaHi, _, hsaF, hsaCap, hsaRes, _, _, _⟩ := henc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [eLo, ← hsaLo]; exact hLo
  · rw [eHi, ← hsaHi]; exact hHi
  · rw [eCap, ← hsaCap]; exact hCap
  · rw [eRes, ← hsaRes]; exact hRes
  · intro i; rw [eFld i, ← hsaF i]; exact hFld i.val i.isLt

/-! ## §10 — THE BOUNDARY: the sovereign-commitment INSTALL is OFF-ROW.

The rebind's defining act — installing `commitmentField := stateCommitment(pre)`, the universe-A
state-commitment of the WHOLE dropped pre-record — has NO EffectVM column. The EffectVM `state_commit`
column is a DIFFERENT commitment (the Poseidon2 H4-of-H4 of the AFTER-block), so the row's commitment
does NOT witness that the pre-record was committed under `stateCommitment`. The row's
`DroppedBlockIntent` only says the readable economic block was ZEROED — NOT that its content was
sovereign-committed. The install soundness lives ONLY in `makeSovereignA_full_sound`. -/

/-- **`makeSovereign_offrow_unenforced` — the loud finding.** `DroppedBlockIntent` is invariant under
any change OUTSIDE the `state_after` economic block — including the (unrepresented) sovereign
commitment install, the receipt, and the guard. Two rows agreeing on the economic after-columns satisfy
the intent equally regardless of what `stateCommitment` value was installed. The row witnesses the
balance-DROP but NOT the commitment INSTALL; that lives ONLY in `makeSovereignA_full_sound`. -/
theorem makeSovereign_offrow_unenforced :
    (∀ env₁ env₂ : VmRowEnv,
      (∀ off : Nat, env₁.loc (saCol off) = env₂.loc (saCol off)) →
      (DroppedBlockIntent env₁ ↔ DroppedBlockIntent env₂)) := by
  intro env₁ env₂ hagree
  unfold DroppedBlockIntent
  rw [hagree state.BALANCE_LO, hagree state.BALANCE_HI, hagree state.NONCE,
      hagree state.CAP_ROOT, hagree state.RESERVED]
  constructor
  · rintro ⟨a, b, c, d, e, f⟩
    exact ⟨a, b, c, d, e, fun i hi => by rw [← hagree (state.FIELD_BASE + i)]; exact f i hi⟩
  · rintro ⟨a, b, c, d, e, f⟩
    exact ⟨a, b, c, d, e, fun i hi => by rw [hagree (state.FIELD_BASE + i)]; exact f i hi⟩

/-! ## §11 — NON-VACUITY. -/

/-- A concrete dropped row: every economic after-column is `0`. -/
def zeroRow : VmRowEnv where
  loc := fun v => if v = SEL_MAKESOVEREIGN then 1 else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- **NON-VACUITY (witness TRUE).** `zeroRow` realizes the dropped-block intent. -/
theorem zeroRow_realizes_intent : DroppedBlockIntent zeroRow := by
  unfold DroppedBlockIntent zeroRow
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (if saCol state.BALANCE_LO = SEL_MAKESOVEREIGN then (1:ℤ) else 0) = 0
    rw [if_neg]; · decide
  · show (if saCol state.BALANCE_HI = SEL_MAKESOVEREIGN then (1:ℤ) else 0) = 0
    rw [if_neg]; · decide
  · show (if saCol state.NONCE = SEL_MAKESOVEREIGN then (1:ℤ) else 0) = 0
    rw [if_neg]; · decide
  · show (if saCol state.CAP_ROOT = SEL_MAKESOVEREIGN then (1:ℤ) else 0) = 0
    rw [if_neg]; · decide
  · show (if saCol state.RESERVED = SEL_MAKESOVEREIGN then (1:ℤ) else 0) = 0
    rw [if_neg]; · decide
  · intro i hi
    show (if saCol (state.FIELD_BASE + i) = SEL_MAKESOVEREIGN then (1:ℤ) else 0) = 0
    rw [if_neg]
    simp only [saCol, STATE_AFTER_BASE, PARAM_BASE, STATE_BEFORE_BASE, NUM_EFFECTS, STATE_SIZE,
      NUM_PARAMS, state.FIELD_BASE, SEL_MAKESOVEREIGN]
    omega

/-- A FORGED row: `zeroRow` with post-`bal_lo` left at `5` (the readable balance survived the rebind). -/
def forgedRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 5 else zeroRow.loc v
  nxt := zeroRow.nxt
  pub := zeroRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `forgedRow`'s post-`bal_lo` is non-zero
(the readable balance survived), so the drop-to-zero gate REJECTS it. -/
theorem forgedRow_rejected : ¬ (gZero state.BALANCE_LO).holdsVm forgedRow false false := by
  apply makeSovereignVm_rejects_surviving_balance
  show (if saCol state.BALANCE_LO = saCol state.BALANCE_LO then (5:ℤ)
    else zeroRow.loc (saCol state.BALANCE_LO)) ≠ 0
  rw [if_pos rfl]; norm_num

/-! ## §12 — axiom-hygiene tripwires. -/

#guard makeSovereignVmDescriptor.constraints.length == 13
#guard makeSovereignVmDescriptor.hashSites.length == 4
#guard makeSovereignVmDescriptor.traceWidth == 186

#assert_axioms makeSovereignVm_faithful
#assert_axioms makeSovereignVm_rejects_nonzero
#assert_axioms makeSovereignVm_rejects_surviving_balance
#assert_axioms makeSovereignVm_commit_binds_block
#assert_axioms sovereignRebind_balOf_zero
#assert_axioms makeSovereign_target_dropped
#assert_axioms makeSovereign_row_matches_executor
#assert_axioms makeSovereign_offrow_unenforced
#assert_axioms zeroRow_realizes_intent
#assert_axioms forgedRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitMakeSovereign

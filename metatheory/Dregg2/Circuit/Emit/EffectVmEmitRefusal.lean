/-
# Dregg2.Circuit.Emit.EffectVmEmitRefusal — the `refusal` effect's EffectVM-row circuit, EMITTED,
RECONCILED onto the RUNNING hand-AIR's columns (cutover convention) and GRADUATED into the descriptor
cutover (v2).

`refusal` writes the `"refusal"` audit slot of `cell`'s RECORD to `1` (dregg1's cross-cell SetState
refusal commitment), BALANCE-NEUTRAL, self-targeted receipt prepended. Its FULL universe-A soundness is
`Inst.RefusalA.refusalA_full_sound ⇒ RefusalSpec` (the EffectSpec layer; all 17 kernel fields + log,
`cell` the ONE touched component — the `refusal := 1` audit write — and every other field frozen).

## THE RUNTIME GROUND TRUTH (the cutover-faithful reconciliation, v2)

The running prover runs `Refusal` (selector 52) as a member of the **Stage-3 passthrough batch**: every
state-block column UNCHANGED EXCEPT the GLOBAL nonce, which TICKS by 1 on this non-NoOp row. The PRE-v2
descriptor FROZE the nonce AND carried NO last-row balance PI binding — so (a) the honest TICKED trace
was UNSAT and (b) the forged-`FINAL_BAL_LO` anti-ghost tooth did not bite. This v2 swaps the nonce-freeze
gate to the runtime TICK gate `gNonce` and appends `transitionAll ++ boundaryFirstPins ++
boundaryLastPins`, so the descriptor AGREES with the hand-AIR AND both anti-ghost teeth bite.

## What the EffectVM row CAN pin

  * the cell's economic block (bal/fields/cap/reserved) is FROZEN; the nonce TICKS by 1 — the refusal
    write is balance-neutral (`auditCellWrite_correct`: a write to a slot `≠ balance` leaves the
    conserved balance untouched);
  * the post-state is bound into `state_commit` (GROUP-4) and published as `NEW_COMMIT`.

## What the EffectVM row CANNOT enforce (the boundary — the WHOLE point of the effect)

  * the `refusal := 1` audit slot write — a NON-`balance` RECORD field, NO EffectVM column;
  * the self-targeted receipt; the three-leg audit guard.

The refusal SOUNDNESS lives ONLY in `refusalA_full_sound`.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; the commitment keystone is UNCONDITIONAL
(a deployed-sponge collision disjunction), never conditioned on the (refuted) injective sponge floor. Read-only imports.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.cellstateaudit

namespace Dregg2.Circuit.Emit.EffectVmEmitRefusal

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA eSub eSelNoop gBalHi gNonce gCapPass gResPass gFieldPass gFieldPassAll
   transitionAll boundaryFirstPins boundaryLastPins
   transferHashSites boundaryLast_pins
   eqToModEq gate_modEq_iff not_modEq_zero_of_canon)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (CellState RowEncodes absorbedCols absorbed_determined_by_commit_or_collides TransferColl)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (refusalField)
open Dregg2.Exec (balanceField)
open Dregg2.Circuit.Spec.CellStateAudit

set_option linter.unusedVariables false

/-! ## §0 — the `refusal` selector column (runtime `sel::REFUSAL = 52`). -/

/-- The `refusal` selector column index (runtime `sel::REFUSAL = 52`). -/
def SEL_REFUSAL : Nat := 52

/-! ## §1 — the per-row gate bodies (RUNTIME-RECONCILED: state-block passthrough + nonce TICK). -/

/-- Balance-lo FREEZE body: `new_bal_lo − old_bal_lo` (balance-neutral; runtime passthrough batch). -/
def gBalLoFreeze : EmittedExpr := eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)

/-- The per-row gates: whole state block PASSTHROUGH + nonce TICK (`gNonce`, runtime convention). -/
def refusalRowGates : List VmConstraint :=
  [ .gate gBalLoFreeze, .gate gBalHi, .gate gNonce
  , .gate gCapPass, .gate gResPass ] ++ gFieldPassAll

/-! ## §2 — the GROUP-4 state-commitment hash sites (reused). -/

def refusalHashSites : List VmHashSite := transferHashSites

/-! ## §3 — the emitted descriptor (v2 = runtime-reconciled, last-row PI pins). -/

def refusalVmAirName : String := "dregg-effectvm-refusal-v2"

/-- **`refusalVmDescriptor`** — the `refusal` EffectVM-row circuit, RECONCILED onto the runtime hand-AIR:
the per-row passthrough gates with the nonce TICK ++ transition continuity ++ the 7 boundary PI pins
(incl. the last-row `FINAL_BAL_LO`/`FINAL_BAL_HI`/`NEW_COMMIT`), the 4 ordered GROUP-4 hash sites and
the 2 balance-limb range checks. -/
def refusalVmDescriptor : EffectVmDescriptor :=
  { name := refusalVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 42
  , constraints := refusalRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
                     ++ selectorGates 52
  , hashSites := refusalHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §4 — the ROW INTENT: state-block passthrough + nonce TICK (runtime-faithful). -/

/-- **`RefusalRowIntent env`** — the intended runtime refusal move: every economic state-block column
UNCHANGED EXCEPT the nonce, which TICKS by 1 (on a non-NoOp row `s_noop = 0`). The audit-slot write +
authority guard are out-of-row (the §off-row finding). FIELD-FAITHFUL: each clause is a congruence
mod `p = 2013265921` (the BabyBear prime) — the deployed circuit enforces the freeze/tick IN THE
FIELD, so the gate set holds IFF this field move holds. -/
def RefusalRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO) ≡ env.loc (sbCol state.BALANCE_LO) [ZMOD 2013265921]
  ∧ env.loc (saCol state.BALANCE_HI) ≡ env.loc (sbCol state.BALANCE_HI) [ZMOD 2013265921]
  ∧ env.loc (saCol state.NONCE)
      ≡ env.loc (sbCol state.NONCE) + (1 - env.loc sel.NOOP) [ZMOD 2013265921]
  ∧ env.loc (saCol state.CAP_ROOT) ≡ env.loc (sbCol state.CAP_ROOT) [ZMOD 2013265921]
  ∧ env.loc (saCol state.RESERVED) ≡ env.loc (sbCol state.RESERVED) [ZMOD 2013265921]
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i))
      ≡ env.loc (sbCol (state.FIELD_BASE + i)) [ZMOD 2013265921])

/-! ## §5 — FAITHFULNESS: the emitted per-row gates ⟺ the runtime-reconciled intent. -/

theorem refusalVm_faithful (env : VmRowEnv) :
    (∀ c ∈ refusalRowGates, c.holdsVm env false false) ↔ RefusalRowIntent env := by
  unfold refusalRowGates gFieldPassAll RefusalRowIntent
  constructor
  · intro h
    have hLo := h (.gate gBalLoFreeze) (by simp)
    have hHi := h (.gate gBalHi) (by simp)
    have hNon := h (.gate gNonce) (by simp)
    have hCap := h (.gate gCapPass) (by simp)
    have hRes := h (.gate gResPass) (by simp)
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (.gate (gFieldPass i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gBalLoFreeze, gBalHi, gNonce, gCapPass, gResPass,
      eSA, eSB, eSub, eSelNoop, EmittedExpr.eval] at hLo hHi hNon hCap hRes
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (gate_modEq_iff (by ring)).mp hLo
    · exact (gate_modEq_iff (by ring)).mp hHi
    · exact (gate_modEq_iff (by ring)).mp hNon
    · exact (gate_modEq_iff (by ring)).mp hCap
    · exact (gate_modEq_iff (by ring)).mp hRes
    · intro i hi
      have hfi := hFld i hi
      simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval] at hfi
      exact (gate_modEq_iff (by ring)).mp hfi
  · rintro ⟨hLo, hHi, hNon, hCap, hRes, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
    · simp only [VmConstraint.holdsVm, gBalLoFreeze, eSA, eSB, eSub, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr hLo
    · simp only [VmConstraint.holdsVm, gBalHi, eSA, eSB, eSub, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr hHi
    · simp only [VmConstraint.holdsVm, gNonce, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr hNon
    · simp only [VmConstraint.holdsVm, gCapPass, eSA, eSB, eSub, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr hCap
    · simp only [VmConstraint.holdsVm, gResPass, eSA, eSB, eSub, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr hRes
    · simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr (hFld i hi)

/-! ## §6 — ANTI-GHOST. -/

theorem refusalVm_rejects_wrong_output (env : VmRowEnv)
    (hwrong : ¬ RefusalRowIntent env) :
    ¬ (∀ c ∈ refusalRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((refusalVm_faithful env).mp h)

/-- **Anti-ghost (balance moved).** A row whose post-`bal_lo` ≠ pre-`bal_lo` fails the freeze gate — a
refusal write cannot silently move value. FIELD-FAITHFUL: the tooth rejects a field-`≢` output, so it
needs the DEPLOYED range-check canonicality — both balance limbs lie in `[0, p)` (the after limb is a
`ranges` wire), so a moved balance differs by less than `p` and the field gate cannot pass by
wrap-around. -/
theorem refusalVm_rejects_moved_balance (env : VmRowEnv)
    (hcanonNew : 0 ≤ env.loc (saCol state.BALANCE_LO)
      ∧ env.loc (saCol state.BALANCE_LO) < 2013265921)
    (hcanonOld : 0 ≤ env.loc (sbCol state.BALANCE_LO)
      ∧ env.loc (sbCol state.BALANCE_LO) < 2013265921)
    (hwrong : env.loc (saCol state.BALANCE_LO) ≠ env.loc (sbCol state.BALANCE_LO)) :
    ¬ (VmConstraint.gate gBalLoFreeze).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoFreeze, eSA, eSB, eSub, EmittedExpr.eval]
  exact not_modEq_zero_of_canon (by ring) hcanonNew hcanonOld hwrong

/-- **Anti-ghost (nonce tamper).** A row whose nonce does NOT tick by 1 fails the reconciled `gNonce`
tick gate — a frozen-nonce trace (the pre-v2 convention) is now correctly UNSAT. FIELD-FAITHFUL: needs
the deployed canonicality — the after-nonce and the ticked pre-nonce both lie in `[0, p)` (nonces are
far below the modulus), so a wrong nonce cannot pass by wrap-around. -/
theorem refusalVm_rejects_nonce_freeze (env : VmRowEnv)
    (hcanonNew : 0 ≤ env.loc (saCol state.NONCE) ∧ env.loc (saCol state.NONCE) < 2013265921)
    (hcanonTick : 0 ≤ env.loc (sbCol state.NONCE) + (1 - env.loc sel.NOOP)
      ∧ env.loc (sbCol state.NONCE) + (1 - env.loc sel.NOOP) < 2013265921)
    (hwrong : env.loc (saCol state.NONCE) ≠ env.loc (sbCol state.NONCE) + (1 - env.loc sel.NOOP)) :
    ¬ (VmConstraint.gate gNonce).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gNonce, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval]
  exact not_modEq_zero_of_canon (by ring) hcanonNew hcanonTick hwrong

/-! ## §7 — the commitment binding: A SECURITY REDUCTION, HOSTED DOWNSTREAM. -/

/-! ⚑ **`refusalVm_commit_binds_block_or_collides` IS DELETED (07-22) — the binding is a SECURITY REDUCTION now, hosted downstream.**

That theorem exported the bare DISJUNCTION `absorbedCols e₁ = absorbedCols e₂ ∨ TransferColl hash e₁ e₂`.
True at deployed BabyBear parameters (unlike its `Poseidon2SpongeCR`-carrying predecessor, which the
deployed compressing sponge REFUTES), but UNCLOSED: a collision EXISTS at those parameters by
pigeonhole, so the `collides` branch is unconditionally available and the binding never has to hold.
A disjunction quantifies over SOLUTIONS; cryptographic hardness quantifies over EFFICIENT ADVERSARIES.

The deployed binding of refusal's absorbed state block is now
`Dregg2.Circuit.Emit.EffectVmCommitReduction.refusal_commit_binds_block_advantage_bound`
(`hEff` discharged at `Eff := IsPolyTime` by `refusal_commit_binds_block_from_polyTime`), whose forgery
game's answers are DEPLOYED refusal ROWS (`refusalVm_row_forgery_is_break`, stated at THIS file's
`refusalHashSites`). It is hosted DOWNSTREAM because the deployed sponge's keyed family
(`Poseidon2KeyedBridge`) transitively imports the effect-emission tree — a reduction stated at that
family cannot be imported by an emission module without a build cycle. -/

/-! ## §8 — the structured per-cell spec (REUSING `CellState`): passthrough + nonce tick. -/

/-- `RowEncodesRefusal env pre post` ties the row's state-block columns to a `(pre, post)` transition. -/
def RowEncodesRefusal (env : VmRowEnv) (pre post : CellState) : Prop :=
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

/-- **`RefusalCellSpec pre post`** — the per-cell FULL-state refusal spec: economic block FROZEN; the
nonce TICKS by 1. FIELD-FAITHFUL: each clause is a mod-`p` congruence (the circuit's denotation lives
in the field; `RowEncodesRefusal`'s decode equalities stay over ℤ). -/
def RefusalCellSpec (pre post : CellState) : Prop :=
  post.balLo ≡ pre.balLo [ZMOD 2013265921]
  ∧ post.balHi ≡ pre.balHi [ZMOD 2013265921]
  ∧ post.nonce ≡ pre.nonce + 1 [ZMOD 2013265921]
  ∧ (∀ i : Fin 8, post.fields i ≡ pre.fields i [ZMOD 2013265921])
  ∧ post.capRoot ≡ pre.capRoot [ZMOD 2013265921]
  ∧ post.reserved ≡ pre.reserved [ZMOD 2013265921]

theorem intent_to_cellSpec (env : VmRowEnv) (pre post : CellState)
    (hnoop : env.loc sel.NOOP = 0)
    (henc : RowEncodesRefusal env pre post) (hint : RefusalRowIntent env) :
    RefusalCellSpec pre post := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hsbC,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes, hsaC, hOld, hNew⟩ := henc
  obtain ⟨hbal, hbhi, hnon, hcap, hres, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hsaLo, ← hsbLo]; exact hbal
  · rw [← hsaHi, ← hsbHi]; exact hbhi
  · rw [← hsaN, ← hsbN]
    have hn := hnon
    rw [hnoop] at hn
    simpa using hn
  · intro i
    have := hfld i.val i.isLt
    rw [← hsaF i, ← hsbF i]; exact this
  · rw [← hsaCap, ← hsbCap]; exact hcap
  · rw [← hsaRes, ← hsbRes]; exact hres

/-! ## §9 — the full descriptor soundness + the commitment binding. -/

theorem refusalDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState) (hnoop : env.loc sel.NOOP = 0)
    (henc : RowEncodesRefusal env pre post)
    (hgatesat : satisfiedVm hash refusalVmDescriptor env true false)
    (hsat : satisfiedVm hash refusalVmDescriptor env true true) :
    RefusalCellSpec pre post ∧ post.commit ≡ env.pub pi.NEW_COMMIT [ZMOD 2013265921] := by
  obtain ⟨hcs, _⟩ := hsat
  obtain ⟨hcsT, _⟩ := hgatesat
  have hgates' : ∀ c ∈ refusalRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ refusalVmDescriptor.constraints := by
      unfold refusalVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
    have := hcsT c hmem
    unfold refusalRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using this
  have hint := (refusalVm_faithful env).mp hgates'
  refine ⟨intent_to_cellSpec env pre post hnoop henc hint, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ refusalVmDescriptor.constraints := by
      unfold refusalVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inr hc)
    have hh := hcs c hmem
    unfold boundaryLastPins at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;>
      · simp only [VmConstraint.holdsVm] at hh ⊢
        exact hh
  have hpin := (boundaryLast_pins env hlast).1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hsaC, _, _⟩ := henc
  rw [← hsaC]; exact hpin

/-! ⚑ **`refusalDescriptor_commit_binds_state_or_collides` IS DELETED (07-22) — the binding is a SECURITY REDUCTION now, hosted downstream.**

That theorem exported the bare DISJUNCTION `absorbedCols e₁ = absorbedCols e₂ ∨ TransferColl hash e₁ e₂`
from two SATISFYING rows sharing a `NEW_COMMIT`. True at deployed BabyBear parameters, but UNCLOSED:
a collision of the compressing sponge EXISTS there by pigeonhole, so the `collides` branch is
unconditionally available and the binding never has to hold.

Its per-effect content — the `boundaryLastPins` step that turns a shared published `NEW_COMMIT` into
a shared `state_commit` COLUMN — survives VERBATIM as the `pinsNewCommit` field of
`Dregg2.Circuit.Emit.EffectVmCommitReduction.refusalNarrowSpec`. The headline is the reduction
`EffectVmCommitReduction.refusalDescriptor_commit_binds_state_advantage_bound` (`hEff` discharged by
`..._from_polyTime`), whose forgery game `narrowDescriptorBreakGame D refusalNarrowSpec` has as its
answers two rows SATISFYING THIS file's `refusalVmDescriptor`. It is hosted DOWNSTREAM because the deployed
sponge's keyed family (`Poseidon2KeyedBridge`) transitively imports the effect-emission tree. -/

/-! ## §10 — CONNECTOR to universe-A `RefusalSpec` via `cellProj`.

`RefusalSpec`'s `cell` clause is `s'.kernel.cell = auditCellMap s.kernel cell refusalField`; since
`refusalField ≠ balanceField`, `auditCellWrite_correct` gives `balOf (post cell) = balOf (pre cell)`. -/

/-- Read cell `c`'s economic block out of the real record-kernel state. -/
def cellProj (k : RecordKernelState) (c : CellId) : CellState where
  balLo    := balOf (k.cell c)
  balHi    := 0
  nonce    := 0
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-- **`refusal_balance_frozen` — the OVERLAP, from the executor.** A committed `refusal` freezes the
cell's economic balance: the `refusal := 1` write lands in a slot `≠ balance`, so `balOf` is preserved
(`auditCellWrite_correct`). -/
theorem refusal_balance_frozen (s s' : RecChainedState) (actor cell : CellId)
    (hspec : RefusalSpec s actor cell s') :
    (cellProj s'.kernel cell).balLo = (cellProj s.kernel cell).balLo := by
  obtain ⟨_, hcellmap, _⟩ := hspec
  show balOf (s'.kernel.cell cell) = balOf (s.kernel.cell cell)
  rw [hcellmap]
  have hf : refusalField ≠ balanceField := by decide
  exact (auditCellWrite_correct s.kernel cell refusalField hf).2.1

/-- **`descriptor_agrees_with_executor_refusal`** — a satisfying run of the runnable descriptor encoding
the refusing cell agrees with the executor's post-state on the FROZEN balance dimension (`balLo`); the
nonce-tick is the runtime cell-bookkeeping leg (off universe-A state). FIELD-FAITHFUL: the circuit
freezes the limb mod `p`; the executor lives over ℤ — canonicality of the two limbs (`[0, p)`, the
deployed range-check + `balOf`'s reduced representation) lifts the field freeze to the ℤ agreement. -/
theorem descriptor_agrees_with_executor_refusal
    (hash : List ℤ → ℤ) (env : VmRowEnv) (hnoop : env.loc sel.NOOP = 0)
    (s s' : RecChainedState) (actor cell : CellId) (pre post : CellState)
    (hpre : pre = cellProj s.kernel cell)
    (hcanonPost : 0 ≤ post.balLo ∧ post.balLo < 2013265921)
    (hcanonPre : 0 ≤ pre.balLo ∧ pre.balLo < 2013265921)
    (henc : RowEncodesRefusal env pre post)
    (hgatesat : satisfiedVm hash refusalVmDescriptor env true false)
    (hsat : satisfiedVm hash refusalVmDescriptor env true true)
    (hspec : RefusalSpec s actor cell s') :
    post.balLo = (cellProj s'.kernel cell).balLo := by
  obtain ⟨hcirc, _⟩ := refusalDescriptor_full_sound hash env pre post hnoop henc hgatesat hsat
  obtain ⟨hcLo, _, _, _, _, _⟩ := hcirc
  have heLo := refusal_balance_frozen s s' actor cell hspec
  -- lift the field freeze `post ≡ pre [ZMOD p]` to ℤ via canonicality of both limbs
  have hz : post.balLo = pre.balLo := by
    have hdvd := Int.modEq_iff_dvd.mp hcLo
    obtain ⟨l₁, u₁⟩ := hcanonPost
    obtain ⟨l₂, u₂⟩ := hcanonPre
    omega
  subst hpre
  rw [hz, heLo]

/-! ## §11 — THE BOUNDARY: the refusal-slot write is OFF-ROW. -/

/-- **`refusal_offrow_unenforced` — the loud finding.** The frozen-frame intent is invariant under any
change OUTSIDE the economic block columns (modulo the `s_noop` nonce tick): two rows agreeing on all
economic columns and `s_noop` satisfy the intent equally, regardless of the (unrepresented) `refusal :=
1` audit slot or receipt. The refusal write is OFF-ROW; the row CANNOT distinguish a refusing cell from
a non-refusing one. -/
theorem refusal_offrow_unenforced :
    (∀ env₁ env₂ : VmRowEnv,
      (∀ off : Nat, env₁.loc (saCol off) = env₂.loc (saCol off) ∧
                     env₁.loc (sbCol off) = env₂.loc (sbCol off)) →
      env₁.loc sel.NOOP = env₂.loc sel.NOOP →
      (RefusalRowIntent env₁ ↔ RefusalRowIntent env₂)) := by
  intro env₁ env₂ hagree hnoop
  unfold RefusalRowIntent
  rw [(hagree state.BALANCE_LO).1, (hagree state.BALANCE_LO).2,
      (hagree state.BALANCE_HI).1, (hagree state.BALANCE_HI).2,
      (hagree state.NONCE).1, (hagree state.NONCE).2, hnoop,
      (hagree state.CAP_ROOT).1, (hagree state.CAP_ROOT).2,
      (hagree state.RESERVED).1, (hagree state.RESERVED).2]
  constructor
  · rintro ⟨a, b, c, d, e, f⟩
    exact ⟨a, b, c, d, e, fun i hi => by
      rw [← (hagree (state.FIELD_BASE + i)).1, ← (hagree (state.FIELD_BASE + i)).2]; exact f i hi⟩
  · rintro ⟨a, b, c, d, e, f⟩
    exact ⟨a, b, c, d, e, fun i hi => by
      rw [(hagree (state.FIELD_BASE + i)).1, (hagree (state.FIELD_BASE + i)).2]; exact f i hi⟩

/-! ## §12 — NON-VACUITY. -/

/-- A concrete refusal row: state-block passthrough + nonce TICK (bal_lo 100 → 100, nonce 5 → 6). -/
def goodRefusalRow : VmRowEnv where
  loc := fun v =>
    if v = SEL_REFUSAL then 1
    else if v = sbCol state.BALANCE_LO then 100
    else if v = saCol state.BALANCE_LO then 100
    else if v = sbCol state.NONCE then 5
    else if v = saCol state.NONCE then 6
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

theorem goodRefusalRow_noop : goodRefusalRow.loc sel.NOOP = 0 := by
  show goodRefusalRow.loc 0 = 0
  simp only [goodRefusalRow, SEL_REFUSAL, sbCol, saCol, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.NONCE]
  norm_num

/-- **NON-VACUITY (witness TRUE).** `goodRefusalRow` REALIZES the runtime refusal intent. -/
theorem goodRefusalRow_realizes_intent : RefusalRowIntent goodRefusalRow := by
  unfold RefusalRowIntent
  have hnoop : goodRefusalRow.loc sel.NOOP = 0 := goodRefusalRow_noop
  refine ⟨eqToModEq rfl, eqToModEq rfl, ?_, eqToModEq rfl, eqToModEq rfl, ?_⟩
  · rw [hnoop]
    apply eqToModEq
    show goodRefusalRow.loc (saCol state.NONCE) = goodRefusalRow.loc (sbCol state.NONCE) + (1 - 0)
    simp only [goodRefusalRow, SEL_REFUSAL, sbCol, saCol, STATE_BEFORE_BASE,
      STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
      state.NONCE]
    norm_num
  · intro i hi
    apply eqToModEq
    show goodRefusalRow.loc (saCol (state.FIELD_BASE + i)) = goodRefusalRow.loc (sbCol (state.FIELD_BASE + i))
    simp only [goodRefusalRow, SEL_REFUSAL, sbCol, saCol, STATE_BEFORE_BASE,
      STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
      state.NONCE, state.FIELD_BASE]
    have e1 : (76 + (3 + i) = 52) = False := eq_false (by omega)
    have e2 : (76 + (3 + i) = 54 + 0) = False := eq_false (by omega)
    have e3 : (76 + (3 + i) = 76 + 0) = False := eq_false (by omega)
    have e4 : (76 + (3 + i) = 54 + 2) = False := eq_false (by omega)
    have e5 : (76 + (3 + i) = 76 + 2) = False := eq_false (by omega)
    have f1 : (54 + (3 + i) = 52) = False := eq_false (by omega)
    have f2 : (54 + (3 + i) = 54 + 0) = False := eq_false (by omega)
    have f3 : (54 + (3 + i) = 76 + 0) = False := eq_false (by omega)
    have f4 : (54 + (3 + i) = 54 + 2) = False := eq_false (by omega)
    have f5 : (54 + (3 + i) = 76 + 2) = False := eq_false (by omega)
    simp only [e1, e2, e3, e4, e5, f1, f2, f3, f4, f5, if_false]

/-- A FORGED refusal row: `goodRefusalRow` with the post-`bal_lo` minted to `999`. -/
def badRefusalRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 999 else goodRefusalRow.loc v
  nxt := goodRefusalRow.nxt
  pub := goodRefusalRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badRefusalRow`'s post-`bal_lo` is forged, so
`gBalLoFreeze` REJECTS it (the concrete `999` and `100` are canonical field elements, so the field
tooth bites with no wrap-around escape). -/
theorem badRefusalRow_rejected : ¬ (VmConstraint.gate gBalLoFreeze).holdsVm badRefusalRow false false := by
  have hsa : badRefusalRow.loc (saCol state.BALANCE_LO) = 999 := by
    simp only [badRefusalRow, goodRefusalRow, sbCol, saCol, SEL_REFUSAL, STATE_BEFORE_BASE,
      STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
      state.NONCE]
    norm_num
  have hsb : badRefusalRow.loc (sbCol state.BALANCE_LO) = 100 := by
    simp only [badRefusalRow, goodRefusalRow, sbCol, saCol, SEL_REFUSAL, STATE_BEFORE_BASE,
      STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
      state.NONCE]
    norm_num
  apply refusalVm_rejects_moved_balance
  · rw [hsa]; norm_num
  · rw [hsb]; norm_num
  · rw [hsa, hsb]; norm_num

/-- A FROZEN-NONCE refusal row: `goodRefusalRow` with the post-nonce held at `5`. -/
def staleNonceRefusalRow : VmRowEnv where
  loc := fun v => if v = saCol state.NONCE then 5 else goodRefusalRow.loc v
  nxt := goodRefusalRow.nxt
  pub := goodRefusalRow.pub

/-- **NON-VACUITY (cutover witness FALSE).** A frozen-nonce row is now correctly UNSAT under the
reconciled `gNonce` tick gate (the concrete `5` and ticked `6` are canonical field elements, so the
field tooth bites with no wrap-around escape). -/
theorem staleNonceRefusalRow_rejected :
    ¬ (VmConstraint.gate gNonce).holdsVm staleNonceRefusalRow false false := by
  have hsa : staleNonceRefusalRow.loc (saCol state.NONCE) = 5 := by
    simp only [staleNonceRefusalRow, goodRefusalRow, sbCol, saCol, SEL_REFUSAL,
      STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS,
      state.BALANCE_LO, state.NONCE]
    norm_num
  have hsb : staleNonceRefusalRow.loc (sbCol state.NONCE) = 5 := by
    simp only [staleNonceRefusalRow, goodRefusalRow, sbCol, saCol, SEL_REFUSAL,
      STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS,
      state.BALANCE_LO, state.NONCE]
    norm_num
  have hnoop : staleNonceRefusalRow.loc sel.NOOP = 0 := by
    simp only [staleNonceRefusalRow, goodRefusalRow, sel.NOOP, sbCol, saCol, SEL_REFUSAL,
      STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS,
      state.BALANCE_LO, state.NONCE]
    norm_num
  apply refusalVm_rejects_nonce_freeze
  · rw [hsa]; norm_num
  · rw [hsb, hnoop]; norm_num
  · rw [hsa, hsb, hnoop]; norm_num

/-! ## §13 — axiom-hygiene tripwires. -/

#guard refusalVmDescriptor.constraints.length == 13 + 14 + 4 + 3 + 1
#guard refusalVmDescriptor.hashSites.length == 4
#guard refusalVmDescriptor.traceWidth == 188

#assert_axioms refusalVm_faithful
#assert_axioms refusalVm_rejects_wrong_output
#assert_axioms refusalVm_rejects_moved_balance
#assert_axioms refusalVm_rejects_nonce_freeze
#assert_axioms intent_to_cellSpec
#assert_axioms refusalDescriptor_full_sound
#assert_axioms refusal_balance_frozen
#assert_axioms descriptor_agrees_with_executor_refusal
#assert_axioms refusal_offrow_unenforced
#assert_axioms goodRefusalRow_realizes_intent
#assert_axioms badRefusalRow_rejected
#assert_axioms staleNonceRefusalRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitRefusal

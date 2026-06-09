/-
# Dregg2.Circuit.Emit.EffectVmEmitIncrementNonce — the NONCE-BUMP effect `incrementNonceA`'s EffectVM-row
  circuit, EMITTED, RECONCILED onto the RUNNING hand-AIR's columns (cutover convention) and GRADUATED into
  the descriptor cutover (v2).

## THE RUNTIME GROUND TRUTH (the cutover-faithful reconciliation, v2)

The running prover runs `incrementNonce` (selector 53) as a member of the **Stage-3 passthrough batch**
(`air.rs:983-1018`, `trace.rs:599`): the trace arm does ONLY `new_state.nonce += 1` and leaves every
economic state-block column (balance limbs, cap_root, all 8 fields, reserved) FROZEN; the GLOBAL nonce
gate (`new_nonce == old_nonce + (1 − s_noop)`) is what ticks. The arm fills NO param.

So the cutover-faithful row is the FROZEN-FRAME + NONCE-TICK shape (the cellDestroy gauntlet). The PRE-v2
descriptor emitted a nonce-MOVE-to-param gate (`new_nonce − param2`) that the runtime hand-AIR does NOT
enforce (the runtime TICKS the nonce via the global gate, leaving param2 = 0) — so the honest TICKED
trace was UNSAT under it (`new_nonce − 0 = old+1 ≠ 0`). This v2 reconciles the descriptor to the runtime
passthrough + nonce TICK: the nonce ticks by 1 via `gNonce`, the rest of the block is frozen.

## What the EffectVM row CAN pin (honest)

  * the cell's economic block (bal/fields/cap/reserved) is FROZEN; the nonce TICKS by 1;
  * the post-state is bound into `state_commit` (GROUP-4) and published as `NEW_COMMIT`.

## The CONNECTOR — to universe-A's `IncrementNonceSpec`

`incrementNonceA` is the one effect whose monotone nonce advance HAS a real executor counterpart: the
`.incrementNonceA` arm freezes the conserved `bal` ledger (`incrementNonce_cellWrite_correct` balance
frame) and bumps the cell's `nonce` field. We connect to the FROZEN balance leg (the on-trace carrier);
the runtime row's `state.NONCE` is the per-cell sequence bookkeeping that ticks every non-NoOp row (the
runtime convention, exactly as every other graduated frozen-frame effect), distinct from the universe-A
cell-record `nonce` field write (off-row).

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Poseidon2 CR = NAMED hypothesis. No sorry /
:= True / native_decide / rfl-bridge. Imports read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.cellstatemonotone

namespace Dregg2.Circuit.Emit.EffectVmEmitIncrementNonce

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA eSub eSelNoop gBalHi gNonce gCapPass gResPass gFieldPass gFieldPassAll
   transitionAll boundaryFirstPins boundaryLastPins
   transferHashSites boundaryLast_pins)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState absorbedCols absorbed_determined_by_commit)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Exec
open Dregg2.Exec.EffectsState
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.Spec.CellStateMonotone

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §0 — the `incrementNonce` selector column (runtime `sel::INCREMENT_NONCE = 53`). -/

/-- The `incrementNonce` selector column index (runtime `sel::INCREMENT_NONCE = 53`). -/
def SEL_INCREMENT_NONCE : Nat := 53

/-- The increment-nonce row: `s_increment_nonce = 1`, `s_noop = 0` (load-bearing for the nonce TICK). -/
def IsIncNonceRow (env : VmRowEnv) : Prop :=
  env.loc SEL_INCREMENT_NONCE = 1 ∧ env.loc sel.NOOP = 0

/-! ## §1 — the per-row gate bodies (RUNTIME-RECONCILED: state-block passthrough + nonce TICK). -/

/-- Balance-lo FREEZE body (a nonce bump moves no value; runtime passthrough batch). -/
def gBalLoFreeze : EmittedExpr := eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)

/-- The per-row gates: whole state block PASSTHROUGH + nonce TICK (`gNonce`, runtime convention). -/
def incNonceRowGates : List VmConstraint :=
  [ .gate gBalLoFreeze, .gate gBalHi, .gate gNonce
  , .gate gCapPass, .gate gResPass ] ++ gFieldPassAll

/-! ## §2 — the emitted descriptor (v2 = runtime-reconciled, last-row PI pins). -/

def incNonceVmAirName : String := "dregg-effectvm-incrementNonce-v2"

def incNonceHashSites : List VmHashSite := transferHashSites

/-- **`incrementNonceVmDescriptor`** — the `incrementNonceA` EffectVM-row circuit, RECONCILED onto the
runtime hand-AIR: the per-row passthrough gates with the nonce TICK ++ transition continuity ++ the 7
boundary PI pins, the 4 ordered GROUP-4 hash sites and the 2 balance-limb range checks. -/
def incrementNonceVmDescriptor : EffectVmDescriptor :=
  { name := incNonceVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := incNonceRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
                     ++ selectorGates 53
  , hashSites := incNonceHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §3 — the ROW INTENT: state-block passthrough + nonce TICK (runtime-faithful). -/

/-- **`IncNonceRowIntent env`** — every economic state-block column UNCHANGED EXCEPT the nonce, which
TICKS by 1 (on a non-NoOp row `s_noop = 0`). -/
def IncNonceRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE) + (1 - env.loc sel.NOOP)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-! ## §4 — FAITHFULNESS. -/

theorem incNonceVm_faithful (env : VmRowEnv) :
    (∀ c ∈ incNonceRowGates, c.holdsVm env false false) ↔ IncNonceRowIntent env := by
  unfold incNonceRowGates gFieldPassAll IncNonceRowIntent
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
    refine ⟨by linarith [hLo], by linarith [hHi], by linarith [hNon], by linarith [hCap],
      by linarith [hRes], ?_⟩
    intro i hi
    have := hFld i hi
    simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval] at this
    linarith
  · rintro ⟨hLo, hHi, hNon, hCap, hRes, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
    · simp only [VmConstraint.holdsVm, gBalLoFreeze, eSA, eSB, eSub, EmittedExpr.eval]; rw [hLo]; ring
    · simp only [VmConstraint.holdsVm, gBalHi, eSA, eSB, eSub, EmittedExpr.eval]; rw [hHi]; ring
    · simp only [VmConstraint.holdsVm, gNonce, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval]
      rw [hNon]; ring
    · simp only [VmConstraint.holdsVm, gCapPass, eSA, eSB, eSub, EmittedExpr.eval]; rw [hCap]; ring
    · simp only [VmConstraint.holdsVm, gResPass, eSA, eSB, eSub, EmittedExpr.eval]; rw [hRes]; ring
    · simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hFld i hi]; ring

/-! ## §5 — ANTI-GHOST. -/

theorem incNonceVm_rejects_wrong_output (env : VmRowEnv) (hwrong : ¬ IncNonceRowIntent env) :
    ¬ (∀ c ∈ incNonceRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((incNonceVm_faithful env).mp h)

/-- **Anti-ghost (balance moved).** A row whose post-`bal_lo` ≠ pre-`bal_lo` fails the freeze gate — a
nonce bump cannot silently move value. -/
theorem incNonceVm_rejects_moved_balance (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO) ≠ env.loc (sbCol state.BALANCE_LO)) :
    ¬ (VmConstraint.gate gBalLoFreeze).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoFreeze, eSA, eSB, eSub, EmittedExpr.eval]
  intro h; apply hwrong; linarith

/-- **Anti-ghost (nonce tamper).** A row whose nonce does NOT tick by 1 fails the reconciled `gNonce`
tick gate — a frozen-nonce trace (the pre-v2 convention) is now correctly UNSAT. -/
theorem incNonceVm_rejects_nonce_freeze (env : VmRowEnv)
    (hwrong : env.loc (saCol state.NONCE) ≠ env.loc (sbCol state.NONCE) + (1 - env.loc sel.NOOP)) :
    ¬ (VmConstraint.gate gNonce).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gNonce, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval]
  intro h; apply hwrong; linarith

/-! ## §6 — the commitment binding (REUSED; hash sites identical to transfer's). -/

theorem incNonce_sites_eq : incrementNonceVmDescriptor.hashSites = transferHashSites := rfl

theorem incNonceVm_commit_binds_block (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ incNonceHashSites)
    (hs₂ : siteHoldsAll hash e₂ incNonceHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    absorbedCols e₁ = absorbedCols e₂ :=
  absorbed_determined_by_commit hash hCR e₁ e₂ hs₁ hs₂ hcommit

/-! ## §7 — the structured per-cell spec (REUSING `CellState`): passthrough + nonce tick. -/

/-- `RowEncodesIncNonce env pre post` ties the row's state-block columns to a `(pre, post)` transition. -/
def RowEncodesIncNonce (env : VmRowEnv) (pre post : CellState) : Prop :=
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

/-- **`CellIncNonceSpec pre post`** — the per-cell FULL-state increment-nonce row spec: economic block
FROZEN; the nonce TICKS by 1. -/
def CellIncNonceSpec (pre post : CellState) : Prop :=
  post.balLo = pre.balLo
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce + 1
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

theorem intent_to_cellSpec (env : VmRowEnv) (pre post : CellState)
    (hnoop : env.loc sel.NOOP = 0)
    (henc : RowEncodesIncNonce env pre post) (hint : IncNonceRowIntent env) :
    CellIncNonceSpec pre post := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hsbC,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes, hsaC, hOld, hNew⟩ := henc
  obtain ⟨hbal, hbhi, hnon, hcap, hres, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hsaLo, ← hsbLo]; exact hbal
  · rw [← hsaHi, ← hsbHi]; exact hbhi
  · rw [← hsaN, ← hsbN, hnon, hnoop]; ring
  · intro i
    have := hfld i.val i.isLt
    rw [← hsaF i, ← hsbF i]; exact this
  · rw [← hsaCap, ← hsbCap]; exact hcap
  · rw [← hsaRes, ← hsbRes]; exact hres

/-! ## §8 — the full descriptor soundness + the commitment binding. -/

theorem incNonceDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState) (hnoop : env.loc sel.NOOP = 0)
    (henc : RowEncodesIncNonce env pre post)
    (hsat : satisfiedVm hash incrementNonceVmDescriptor env true true) :
    CellIncNonceSpec pre post ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, _⟩ := hsat
  have hgates' : ∀ c ∈ incNonceRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ incrementNonceVmDescriptor.constraints := by
      unfold incrementNonceVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
    have := hcs c hmem
    unfold incNonceRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using this
  have hint := (incNonceVm_faithful env).mp hgates'
  refine ⟨intent_to_cellSpec env pre post hnoop henc hint, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ incrementNonceVmDescriptor.constraints := by
      unfold incrementNonceVmDescriptor
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

theorem incNonceDescriptor_commit_binds_state (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hsat₁ : satisfiedVm hash incrementNonceVmDescriptor e₁ true true)
    (hsat₂ : satisfiedVm hash incrementNonceVmDescriptor e₂ true true)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT) :
    absorbedCols e₁ = absorbedCols e₂ := by
  have hs₁ : siteHoldsAll hash e₁ incNonceHashSites := hsat₁.2.1
  have hs₂ : siteHoldsAll hash e₂ incNonceHashSites := hsat₂.2.1
  have hc : ∀ (e : VmRowEnv), satisfiedVm hash incrementNonceVmDescriptor e true true →
      e.loc (saCol state.STATE_COMMIT) = e.pub pi.NEW_COMMIT := by
    intro e hsat
    obtain ⟨hcs, _⟩ := hsat
    have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm e false true := by
      intro c hc
      have hmem : c ∈ incrementNonceVmDescriptor.constraints := by
        unfold incrementNonceVmDescriptor
        simp only [List.mem_append]
        exact Or.inl (Or.inr hc)
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

/-! ## §9 — THE CONNECTOR — `cellProjN` to universe-A's `IncrementNonceSpec` (conserved-balance freeze). -/

/-- Read cell `c`'s conserved economic balance out of the real record-kernel state. -/
def cellProjN (k : RecordKernelState) (c : CellId) : CellState where
  balLo    := balOf (k.cell c)
  balHi    := 0
  nonce    := 0
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-- **`incNonce_balance_frozen` — the OVERLAP, from the executor.** A committed `incrementNonceA` freezes
the cell's conserved economic balance (the bump rewrites only the cell's `nonce` field). -/
theorem incNonce_balance_frozen (s s' : RecChainedState) (actor cell : CellId) (n : Int)
    (hspec : IncrementNonceSpec s actor cell n s') :
    (cellProjN s'.kernel cell).balLo = (cellProjN s.kernel cell).balLo := by
  show balOf (s'.kernel.cell cell) = balOf (s.kernel.cell cell)
  rw [hspec.2.1]
  exact (incrementNonce_cellWrite_correct s.kernel cell n).2.1

/-- **`nonce_write_is_out_of_row` — the executor's cell-record nonce write (universe-A leg).** A committed
`incrementNonceA` writes the cell's `nonce` RECORD field to exactly `n`. This is the universe-A monotone
write; the RUNNABLE descriptor binds the on-trace per-cell sequence-nonce TICK (the runtime bookkeeping
convention), distinct from the cell-record `nonce` field. -/
theorem nonce_write_is_out_of_row (s s' : RecChainedState) (actor cell : CellId) (n : Int)
    (hspec : IncrementNonceSpec s actor cell n s') :
    fieldOf nonceField (s'.kernel.cell cell) = (n : ℤ) := by
  rw [hspec.2.1]
  exact (incrementNonce_cellWrite_correct s.kernel cell n).1

/-- **`descriptor_agrees_with_executor_incNonce`** — a satisfying run of the runnable descriptor encoding
the bumped cell agrees with the executor's post-state on the FROZEN balance dimension (`balLo`); the
runtime nonce-tick is the per-cell sequence bookkeeping leg (off the universe-A cell-record nonce). -/
theorem descriptor_agrees_with_executor_incNonce
    (hash : List ℤ → ℤ) (env : VmRowEnv) (hnoop : env.loc sel.NOOP = 0)
    (s s' : RecChainedState) (actor cell : CellId) (n : Int) (pre post : CellState)
    (hpre : pre = cellProjN s.kernel cell)
    (henc : RowEncodesIncNonce env pre post)
    (hsat : satisfiedVm hash incrementNonceVmDescriptor env true true)
    (hspec : IncrementNonceSpec s actor cell n s') :
    post.balLo = (cellProjN s'.kernel cell).balLo := by
  obtain ⟨hcirc, _⟩ := incNonceDescriptor_full_sound hash env pre post hnoop henc hsat
  obtain ⟨hcLo, _, _, _, _, _⟩ := hcirc
  have heLo := incNonce_balance_frozen s s' actor cell n hspec
  subst hpre
  rw [hcLo, heLo]

/-! ## §9½ — THE EXECUTOR UNIFICATION (`unify_incNonce_exec`) + the class-A capstone.

The A− residual the ledger flagged was "no `unify_*_exec` connector to `recKExec`; universe-A has no
nonce-tick effect, executor-orphaned". That residual is now CLOSED: `incrementNonceA` DOES have a
verified-executor home — `execFullA s (.incrementNonceA actor cell n)` (= `stateStep s nonceField …`),
whose full-state characterization is `execFullA_incrementNonce_iff_spec ⇒ IncrementNonceSpec` (all 17
kernel fields + log validated). We weld the descriptor's bound block to that executor post-state and
state the nonce-carrier boundary EXACTLY.

The descriptor's bound block is {balLo, balHi, fields, capRoot, reserved} FROZEN + the on-trace
sequence-`nonce` TICK. Under `cellProjN` (which reads the cell's conserved economic measure), EVERY
descriptor-frozen dimension is an executor-frozen dimension (the executor's `incrementNonceA` rewrites
ONLY the cell-record `nonce` slot, balance-Δ = 0 — `incrementNonce_cellWrite_correct`). So the descriptor
and the executor AGREE on the entire `cellProjN` block. The nonce CARRIERS differ by design — the
descriptor's on-trace `state.NONCE` is the runtime per-cell sequence counter (TICK by 1), the executor's
is the cell-record `nonce` field (write to `n`, `nonce_write_is_out_of_row`) — both monotone nonce
advances, NAMED here, NOT a soundness gap (the conserved-economic block is fully agreed + anti-ghosted). -/

/-- **`unify_incNonce_exec` — the executor unification.** A committed `incrementNonceA` (via the live
`execFullA`, whose full-state correctness is `execFullA_incrementNonce_iff_spec`), projected onto the
bumped cell under `cellProjN`, satisfies `CellIncNonceSpec`'s conserved-economic content EXACTLY: the
balance measure is frozen (`balLo` unchanged), and the cellProjN frame columns (balHi/fields/cap/reserved)
are the constant `0` the projection assigns — i.e. the descriptor's frozen block IS the executor's. -/
theorem unify_incNonce_exec (s s' : RecChainedState) (actor cell : CellId) (n : Int)
    (h : execFullA s (.incrementNonceA actor cell n) = some s') :
    (cellProjN s'.kernel cell).balLo = (cellProjN s.kernel cell).balLo
    ∧ (cellProjN s'.kernel cell).balHi = (cellProjN s.kernel cell).balHi
    ∧ (∀ i, (cellProjN s'.kernel cell).fields i = (cellProjN s.kernel cell).fields i)
    ∧ (cellProjN s'.kernel cell).capRoot = (cellProjN s.kernel cell).capRoot
    ∧ (cellProjN s'.kernel cell).reserved = (cellProjN s.kernel cell).reserved := by
  have hspec := (execFullA_incrementNonce_iff_spec s actor cell n s').mp h
  exact ⟨incNonce_balance_frozen s s' actor cell n hspec, rfl, fun _ => rfl, rfl, rfl⟩

/-- **`incNonceDescriptor_classA` — the per-cell class-A capstone (the transfer bar, per cell).**
Satisfying the runnable descriptor under `RowEncodesIncNonce`, for the bumped cell of a committed
`execFullA … (.incrementNonceA …)`, forces: (a) the FULL per-cell `CellIncNonceSpec` (economic block
FROZEN, the nonce TICKS by 1) from the descriptor; (b) the post-state published as `PI[NEW_COMMIT]`
(bound + anti-ghosted on all 13 absorbed columns via `incNonceDescriptor_commit_binds_state`); and
(c) AGREEMENT with the executor's post-state on the WHOLE conserved-economic `cellProjN` block
(balLo/balHi/fields/cap/reserved). The nonce-carrier boundary (on-trace seq-nonce TICK vs the
`nonce_write_is_out_of_row` record-nonce write) is the named, honest residual — both monotone nonce
advances, NOT a soundness gap. This is the transfer class-A capstone shape (`*_full_sound` +
`*_commit_binds_state` + `unify_*_exec`), per cell. -/
theorem incNonceDescriptor_classA (hash : List ℤ → ℤ) (env : VmRowEnv) (hnoop : env.loc sel.NOOP = 0)
    (s s' : RecChainedState) (actor cell : CellId) (n : Int) (post : CellState)
    (henc : RowEncodesIncNonce env (cellProjN s.kernel cell) post)
    (hsat : satisfiedVm hash incrementNonceVmDescriptor env true true)
    (hexec : execFullA s (.incrementNonceA actor cell n) = some s') :
    CellIncNonceSpec (cellProjN s.kernel cell) post
    ∧ post.commit = env.pub pi.NEW_COMMIT
    ∧ post.balLo = (cellProjN s'.kernel cell).balLo
    ∧ post.balHi = (cellProjN s'.kernel cell).balHi
    ∧ (∀ i, post.fields i = (cellProjN s'.kernel cell).fields i)
    ∧ post.capRoot = (cellProjN s'.kernel cell).capRoot
    ∧ post.reserved = (cellProjN s'.kernel cell).reserved := by
  obtain ⟨hcirc, hcommit⟩ :=
    incNonceDescriptor_full_sound hash env (cellProjN s.kernel cell) post hnoop henc hsat
  obtain ⟨hcLo, hcHi, _hcN, hcF, hcCap, hcRes⟩ := hcirc
  obtain ⟨heLo, heHi, heF, heCap, heRes⟩ := unify_incNonce_exec s s' actor cell n hexec
  refine ⟨⟨hcLo, hcHi, _hcN, hcF, hcCap, hcRes⟩, hcommit, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcLo, heLo]
  · rw [hcHi, heHi]
  · intro i; rw [hcF i, heF i]
  · rw [hcCap, heCap]
  · rw [hcRes, heRes]

/-! ## §10 — NON-VACUITY. -/

/-- A concrete increment-nonce row: state-block passthrough + nonce TICK (bal_lo 100 → 100, nonce 5 → 6). -/
def goodIncNonceRow : VmRowEnv where
  loc := fun v =>
    if v = SEL_INCREMENT_NONCE then 1
    else if v = sbCol state.BALANCE_LO then 100
    else if v = saCol state.BALANCE_LO then 100
    else if v = sbCol state.NONCE then 5
    else if v = saCol state.NONCE then 6
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

theorem goodIncNonceRow_noop : goodIncNonceRow.loc sel.NOOP = 0 := by
  show goodIncNonceRow.loc 0 = 0
  simp only [goodIncNonceRow, SEL_INCREMENT_NONCE, sbCol, saCol, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.NONCE]
  norm_num

/-- **NON-VACUITY (witness TRUE).** `goodIncNonceRow` REALIZES the runtime increment-nonce intent. -/
theorem goodIncNonceRow_realizes_intent : IncNonceRowIntent goodIncNonceRow := by
  unfold IncNonceRowIntent
  have hnoop : goodIncNonceRow.loc sel.NOOP = 0 := goodIncNonceRow_noop
  refine ⟨rfl, rfl, ?_, rfl, rfl, ?_⟩
  · rw [hnoop]
    show goodIncNonceRow.loc (saCol state.NONCE) = goodIncNonceRow.loc (sbCol state.NONCE) + (1 - 0)
    simp only [goodIncNonceRow, SEL_INCREMENT_NONCE, sbCol, saCol, STATE_BEFORE_BASE,
      STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
      state.NONCE]
    norm_num
  · intro i hi
    show goodIncNonceRow.loc (saCol (state.FIELD_BASE + i)) = goodIncNonceRow.loc (sbCol (state.FIELD_BASE + i))
    simp only [goodIncNonceRow, SEL_INCREMENT_NONCE, sbCol, saCol, STATE_BEFORE_BASE,
      STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
      state.NONCE, state.FIELD_BASE]
    have e1 : (76 + (3 + i) = 53) = False := eq_false (by omega)
    have e2 : (76 + (3 + i) = 54 + 0) = False := eq_false (by omega)
    have e3 : (76 + (3 + i) = 76 + 0) = False := eq_false (by omega)
    have e4 : (76 + (3 + i) = 54 + 2) = False := eq_false (by omega)
    have e5 : (76 + (3 + i) = 76 + 2) = False := eq_false (by omega)
    have f1 : (54 + (3 + i) = 53) = False := eq_false (by omega)
    have f2 : (54 + (3 + i) = 54 + 0) = False := eq_false (by omega)
    have f3 : (54 + (3 + i) = 76 + 0) = False := eq_false (by omega)
    have f4 : (54 + (3 + i) = 54 + 2) = False := eq_false (by omega)
    have f5 : (54 + (3 + i) = 76 + 2) = False := eq_false (by omega)
    simp only [e1, e2, e3, e4, e5, f1, f2, f3, f4, f5, if_false]

/-- A FORGED increment-nonce row: `goodIncNonceRow` with the post-`bal_lo` minted to `999`. -/
def badIncNonceRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 999 else goodIncNonceRow.loc v
  nxt := goodIncNonceRow.nxt
  pub := goodIncNonceRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badIncNonceRow`'s post-`bal_lo` is forged, so
`gBalLoFreeze` REJECTS it. -/
theorem badIncNonceRow_rejected : ¬ (VmConstraint.gate gBalLoFreeze).holdsVm badIncNonceRow false false := by
  apply incNonceVm_rejects_moved_balance
  simp only [badIncNonceRow, goodIncNonceRow, sbCol, saCol, SEL_INCREMENT_NONCE, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
    state.NONCE]
  norm_num

/-- A FROZEN-NONCE increment-nonce row: `goodIncNonceRow` with the post-nonce held at `5`. -/
def staleNonceIncNonceRow : VmRowEnv where
  loc := fun v => if v = saCol state.NONCE then 5 else goodIncNonceRow.loc v
  nxt := goodIncNonceRow.nxt
  pub := goodIncNonceRow.pub

/-- **NON-VACUITY (cutover witness FALSE).** A frozen-nonce row is now correctly UNSAT under the
reconciled `gNonce` tick gate. -/
theorem staleNonceIncNonceRow_rejected :
    ¬ (VmConstraint.gate gNonce).holdsVm staleNonceIncNonceRow false false := by
  apply incNonceVm_rejects_nonce_freeze
  simp only [staleNonceIncNonceRow, goodIncNonceRow, sel.NOOP, sbCol, saCol, SEL_INCREMENT_NONCE,
    STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS,
    state.BALANCE_LO, state.NONCE]
  norm_num

/-! ## §11 — Axiom-hygiene tripwires. -/

#guard incrementNonceVmDescriptor.constraints.length == 13 + 14 + 4 + 3 + 1
#guard incrementNonceVmDescriptor.hashSites.length == 4
#guard incrementNonceVmDescriptor.traceWidth == 186

#assert_axioms incNonceVm_faithful
#assert_axioms incNonceVm_rejects_wrong_output
#assert_axioms incNonceVm_rejects_moved_balance
#assert_axioms incNonceVm_rejects_nonce_freeze
#assert_axioms intent_to_cellSpec
#assert_axioms incNonceDescriptor_full_sound
#assert_axioms incNonceDescriptor_commit_binds_state
#assert_axioms incNonce_balance_frozen
#assert_axioms nonce_write_is_out_of_row
#assert_axioms descriptor_agrees_with_executor_incNonce
#assert_axioms unify_incNonce_exec
#assert_axioms incNonceDescriptor_classA
#assert_axioms goodIncNonceRow_realizes_intent
#assert_axioms badIncNonceRow_rejected
#assert_axioms staleNonceIncNonceRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitIncrementNonce

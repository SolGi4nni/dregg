/-
# Dregg2.Exec.TurnAdmission — compose the admission prologue with the gated call-forest executor.

`Admission.runTurn` is the fail-closed prologue (fee + nonce + replay + receipt-chain binding) that
dregg1 runs BEFORE the forest fold. `FullForestAuth.execFullForestG` is the production forest executor
with per-node credential+caveat gates. This module wires them together as the devnet-shaped entry:

    runGatedForestTurn ctx hdr pre forest = runTurn ctx hdr pre (execFullForestG · forest)

The prologue commits even when the gated forest body fails (`prologue_survives_failed_body`); an
inadmissible turn is rejected with no edit (`runTurn_inadmissible_rejects`).

ADDITIVE: imports `Admission` + `FullForestAuth`; edits none.
-/
import Dregg2.Exec.Admission
import Dregg2.Exec.GatedForestCfg
import Dregg2.Exec.HandlerExecutor

namespace Dregg2.Exec.TurnAdmission

open Dregg2.Exec (balOf)
open Dregg2.Exec.Admission
open Dregg2.Exec.EffectTransfer (nonceOf)
open Dregg2.Exec.FullForestAuth
open Dregg2.Exec.HandlerExecutor (execHandlerTurn)
open Dregg2.Exec.StarbridgeGated (DForest St Wt)
open Dregg2.Exec.TurnExecutorFull (FullActionA)

/-- **Devnet-shaped turn execution:** admission prologue ∘ gated call-forest body ∘ fee distribution.

A2: the FAITHFUL `execute.rs` flow — PHASE 1 prologue (fee debit, never rolled back), the rollback-able
gated forest body, and (Phase 3, ONLY on a committing body) `distributeFee` credits the proposer 50% +
treasury 30%, the residue burned. Conservation holds MODULO BURN across the full turn including the
prologue (`Admission.fee_conservation_modulo_burn`). On a body abort the prologue survives WITHOUT
distribution (matching Rust: distribution runs only after successful forest execution). -/
def runGatedForestTurn (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (forest : DForest) : Option RecChainedState :=
  runTurn ctx h s (fun s₁ => (execFullForestG s₁ forest).map (fun s₂ => distributeFee ctx s₂ h.fee))

/-- **Handler-cutover turn execution:** admission prologue ∘ flat `execHandlerTurn` action list.
The soundness-strengthening path: the wire tree is lowered (`lowerForestA (eraseAuth root)`) and
dispatched through the proved handler registry — no per-node credential gate on the body. -/
def runHandlerTurn (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (acts : List FullActionA) : Option RecChainedState :=
  runTurn ctx h s (fun s₁ => execHandlerTurn acts s₁)

/-! ## §STATUS — the THREE-WAY turn outcome (boundary-P1 bug 2).

`runTurn`/`runGatedForestTurn` return `Option RecChainedState`, and the C export collapsed BOTH
`some (commitPrologue …)` (admission passed but the BODY FAILED — e.g. a forged credential rolled the
forest back, only the never-rolled-back fee/nonce prologue survives) AND `some s'` (body
committed) to the SAME `ok:1`. A forged-credential turn therefore reported `ok:1` and was treated as a
committed/accepted turn by the node — taking the attacker's word that the body succeeded.

`TurnStatus` distinguishes the three real outcomes so the C boundary can report `BodyCommitted` ONLY
when the forest body actually committed. A `PrologueCommittedBodyFailed` result charges the fee
(anti-spam) but the turn is REJECTED — it must NOT be treated as an accepted turn. -/

/-- The three-way result of a turn: the body committed, the body failed but the prologue
(fee/nonce) was committed (anti-spam, NOT an accepted turn), or admission rejected it (no edit). -/
inductive TurnStatus
  /-- Admission failed: rejected with NO state edit. -/
  | rejected
  /-- Admission passed, the prologue (fee debit + nonce tick) was committed and is never rolled
  back, but the BODY FAILED (a forged credential / failed effect / violated caveat rolled the forest
  back). The fee may be charged as anti-spam, but **the turn is REJECTED** — not an accepted turn. -/
  | prologueCommittedBodyFailed
  /-- Admission passed AND the body committed: the turn is ACCEPTED. -/
  | bodyCommitted
deriving Repr, DecidableEq

/-- The status-bearing turn executor: like `runTurn` but the result records WHICH of the three
outcomes occurred. The body-success arm yields `bodyCommitted`; the body-failure arm yields
`prologueCommittedBodyFailed` (with the prologue state, never rolled back); inadmissible yields
`rejected` (no state). -/
def runTurnStatus (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (body : RecChainedState → Option RecChainedState) : TurnStatus × Option RecChainedState :=
  if admissible ctx h s = true then
    let s₁ := commitPrologue s h.agent h.fee
    match body s₁ with
    | some s' => (TurnStatus.bodyCommitted, some s')
    | none    => (TurnStatus.prologueCommittedBodyFailed, some s₁)
  else
    (TurnStatus.rejected, none)

/-- `runTurnStatus`'s state projection agrees with `runTurn` exactly: the status is the NEW
information, the state is unchanged. -/
theorem runTurnStatus_state (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (body : RecChainedState → Option RecChainedState) :
    (runTurnStatus ctx h s body).2 = runTurn ctx h s body := by
  unfold runTurnStatus runTurn
  by_cases hadm : admissible ctx h s = true
  · simp only [if_pos hadm]; cases body (commitPrologue s h.agent h.fee) <;> rfl
  · simp only [if_neg hadm]

/-- **THE KEY BOUNDARY THEOREM (bug 2).** The status is `bodyCommitted` IFF admission passed AND the
body returned `some`. So a turn whose body FAILS (forged credential, violated caveat, failed effect)
is NEVER `bodyCommitted` — the C boundary cannot be tricked into reporting acceptance. -/
theorem runTurnStatus_bodyCommitted_iff (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (body : RecChainedState → Option RecChainedState) :
    (runTurnStatus ctx h s body).1 = TurnStatus.bodyCommitted
      ↔ admissible ctx h s = true ∧ (body (commitPrologue s h.agent h.fee)).isSome := by
  unfold runTurnStatus
  by_cases hadm : admissible ctx h s = true
  · simp only [if_pos hadm, hadm, true_and]
    cases hb : body (commitPrologue s h.agent h.fee) <;> simp [hb]
  · simp only [if_neg hadm]
    constructor
    · intro h'; cases h'
    · intro ⟨hc, _⟩; exact absurd hc hadm

/-- **bug-2 corollary: a failing body is NOT `bodyCommitted`.** If the body fails, the status is
`prologueCommittedBodyFailed` — the fee/nonce prologue survives (anti-spam) but the turn is rejected. -/
theorem runTurnStatus_failed_body (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (body : RecChainedState → Option RecChainedState)
    (hadm : admissible ctx h s = true)
    (hbody : body (commitPrologue s h.agent h.fee) = none) :
    (runTurnStatus ctx h s body).1 = TurnStatus.prologueCommittedBodyFailed := by
  unfold runTurnStatus; simp only [if_pos hadm, hbody]

/-- A failing body is, in particular, NOT `bodyCommitted` (the contrapositive the boundary relies on). -/
theorem runTurnStatus_failed_body_not_committed (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (body : RecChainedState → Option RecChainedState)
    (hadm : admissible ctx h s = true)
    (hbody : body (commitPrologue s h.agent h.fee) = none) :
    (runTurnStatus ctx h s body).1 ≠ TurnStatus.bodyCommitted := by
  rw [runTurnStatus_failed_body ctx h s body hadm hbody]; decide

/-- An inadmissible turn's status is `rejected` (no state edit). -/
theorem runTurnStatus_rejected (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (body : RecChainedState → Option RecChainedState)
    (hbad : admissible ctx h s = false) :
    (runTurnStatus ctx h s body).1 = TurnStatus.rejected ∧ (runTurnStatus ctx h s body).2 = none := by
  unfold runTurnStatus; simp only [hbad]; exact ⟨rfl, rfl⟩

#assert_axioms runTurnStatus_state
#assert_axioms runTurnStatus_bodyCommitted_iff
#assert_axioms runTurnStatus_failed_body
#assert_axioms runTurnStatus_failed_body_not_committed
#assert_axioms runTurnStatus_rejected

/-- **Status-bearing gated forest turn** (the production path with three-way outcome). The body is
the gated forest THEN fee distribution; the status records whether that body committed. -/
def runGatedForestTurnStatus (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (forest : DForest) : TurnStatus × Option RecChainedState :=
  runTurnStatus ctx h s (fun s₁ => (execFullForestG s₁ forest).map (fun s₂ => distributeFee ctx s₂ h.fee))

/-- The status-bearing variant projects to `runGatedForestTurn` on the state. -/
theorem runGatedForestTurnStatus_state (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (forest : DForest) :
    (runGatedForestTurnStatus ctx h s forest).2 = runGatedForestTurn ctx h s forest :=
  runTurnStatus_state ctx h s _

/-- **bug-2 production corollary: a turn whose GATED FOREST BODY fails (e.g. a forged credential
rolls the forest back) is NOT `bodyCommitted`.** The prologue fee/nonce survive (anti-spam) but the
status is `prologueCommittedBodyFailed` — the node must NOT treat it as an accepted turn. -/
theorem runGatedForestTurnStatus_forged_not_committed (ctx : AdmCtx) (h : TurnHdr)
    (s : RecChainedState) (forest : DForest)
    (hadm : admissible ctx h s = true)
    (hbody : execFullForestG (commitPrologue s h.agent h.fee) forest = none) :
    (runGatedForestTurnStatus ctx h s forest).1 = TurnStatus.prologueCommittedBodyFailed := by
  unfold runGatedForestTurnStatus
  refine runTurnStatus_failed_body ctx h s _ hadm ?_
  simp [hbody]

#assert_axioms runGatedForestTurnStatus_state
#assert_axioms runGatedForestTurnStatus_forged_not_committed

/-- The composed body: gated forest THEN (on commit) fee distribution. -/
private def gfBody (ctx : AdmCtx) (h : TurnHdr) (forest : DForest) :
    RecChainedState → Option RecChainedState :=
  fun s₁ => (execFullForestG s₁ forest).map (fun s₂ => distributeFee ctx s₂ h.fee)

theorem runGatedForestTurn_inadmissible_rejects (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (forest : DForest) (hbad : admissible ctx h s = false) :
    runGatedForestTurn ctx h s forest = none :=
  runTurn_inadmissible_rejects ctx h s (gfBody ctx h forest) hbad

theorem runGatedForestTurn_failed_body_commits_prologue (ctx : AdmCtx) (h : TurnHdr)
    (s : RecChainedState) (forest : DForest)
    (hadm : admissible ctx h s = true)
    (hbody : execFullForestG (commitPrologue s h.agent h.fee) forest = none) :
    runGatedForestTurn ctx h s forest = some (commitPrologue s h.agent h.fee) := by
  unfold runGatedForestTurn
  refine runTurn_failed_body ctx h s (gfBody ctx h forest) hadm ?_
  simp [gfBody, hbody]

theorem runGatedForestTurn_prologue_survives_failed_body (ctx : AdmCtx) (h : TurnHdr)
    (s : RecChainedState) (forest : DForest)
    (hadm : admissible ctx h s = true)
    (hbody : execFullForestG (commitPrologue s h.agent h.fee) forest = none) :
    ∃ s', runGatedForestTurn ctx h s forest = some s' ∧
      balOf (s'.kernel.cell h.agent) = balOf (s.kernel.cell h.agent) - h.fee ∧
      nonceOf (s'.kernel.cell h.agent) = nonceOf (s.kernel.cell h.agent) + 1 := by
  refine prologue_survives_failed_body ctx h s (gfBody ctx h forest) hadm ?_
  simp [gfBody, hbody]

/-- A2 — on a COMMITTING body, the turn distributes the fee: the post-state is
`distributeFee ctx s' h.fee` (proposer +fee/2, treasury +fee*3/10, residue burned). -/
theorem runGatedForestTurn_committing_body (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (forest : DForest) (s' : RecChainedState)
    (hadm : admissible ctx h s = true)
    (hbody : execFullForestG (commitPrologue s h.agent h.fee) forest = some s') :
    runGatedForestTurn ctx h s forest = some (distributeFee ctx s' h.fee) := by
  unfold runGatedForestTurn
  refine prologue_then_commit ctx h s (gfBody ctx h forest) (distributeFee ctx s' h.fee) hadm ?_
  simp [gfBody, hbody]

/-- **A2 end-to-end conservation-modulo-burn.** On a committing turn over THREE DISTINCT fee
cells, the {agent, proposer, treasury} triple's total after the FULL turn (prologue ∘ body ∘ distribute)
equals the triple total over the POST-PROLOGUE PRE-DISTRIBUTION state `s` (the original, with the
prologue's −fee already counted via `commitPrologue`) MINUS exactly `feeBurned h.fee`. Concretely: the
distribution credits the triple `fee − feeBurned` (proposer + treasury shares) on top of the prologue's
−fee, so relative to the ORIGINAL pre-turn `s` the triple's net change is `−feeBurned` — conserved modulo
the protocol burn, no silent loss. (Body assumed triple-neutral on the agent/p/t cells, the usual case:
a fee turn whose forest does not itself move balances among the three fee cells.) -/
theorem runGatedForestTurn_conserves_modulo_burn (ctx : AdmCtx) (h : TurnHdr) (s s' : RecChainedState)
    (forest : DForest) (p t : CellId)
    (hadm : admissible ctx h s = true)
    (hbody : execFullForestG (commitPrologue s h.agent h.fee) forest = some s')
    (hp : ctx.proposer = some p) (ht : ctx.treasury = some t)
    (hap : h.agent ≠ p) (hat : h.agent ≠ t) (hpt : p ≠ t)
    -- the forest body left the three fee cells' balances at their post-prologue values:
    (hbA : balOf (s'.kernel.cell h.agent) = balOf ((commitPrologue s h.agent h.fee).kernel.cell h.agent))
    (hbP : balOf (s'.kernel.cell p) = balOf ((commitPrologue s h.agent h.fee).kernel.cell p))
    (hbT : balOf (s'.kernel.cell t) = balOf ((commitPrologue s h.agent h.fee).kernel.cell t)) :
    ∃ sf, runGatedForestTurn ctx h s forest = some sf ∧
      feeTriSum sf h.agent p t = feeTriSum s h.agent p t - feeBurned h.fee := by
  refine ⟨distributeFee ctx s' h.fee, runGatedForestTurn_committing_body ctx h s forest s' hadm hbody, ?_⟩
  -- distributeFee credits p (+fee/2) and t (+fee*3/10); agent untouched.
  have hagent : balOf ((distributeFee ctx s' h.fee).kernel.cell h.agent) = balOf (s'.kernel.cell h.agent) := by
    rw [distributeFee_frame ctx s' h.fee p t h.agent hp ht hap hat]
  have hprop : balOf ((distributeFee ctx s' h.fee).kernel.cell p)
      = balOf (s'.kernel.cell p) + proposerShare h.fee := by
    simp only [distributeFee, creditOpt, hp, ht]
    rw [creditCell_frame _ _ _ _ hpt, creditCell_balance]
  have htreas : balOf ((distributeFee ctx s' h.fee).kernel.cell t)
      = balOf (s'.kernel.cell t) + treasuryShare h.fee := by
    simp only [distributeFee, creditOpt, hp, ht]
    rw [creditCell_balance, creditCell_frame _ _ _ _ (Ne.symm hpt)]
  -- the prologue's effect on the triple cells (agent −fee, p/t untouched):
  have hpA : balOf ((commitPrologue s h.agent h.fee).kernel.cell h.agent) = balOf (s.kernel.cell h.agent) - h.fee :=
    commitPrologue_balance s h.agent h.fee
  have hpP : balOf ((commitPrologue s h.agent h.fee).kernel.cell p) = balOf (s.kernel.cell p) :=
    congrArg balOf (commitPrologue_frame s h.agent h.fee p (Ne.symm hap))
  have hpT : balOf ((commitPrologue s h.agent h.fee).kernel.cell t) = balOf (s.kernel.cell t) :=
    congrArg balOf (commitPrologue_frame s h.agent h.fee t (Ne.symm hat))
  simp only [feeTriSum, hagent, hprop, htreas, hbA, hbP, hbT, hpA, hpP, hpT, feeBurned]; ring

#assert_axioms runGatedForestTurn_inadmissible_rejects
#assert_axioms runGatedForestTurn_failed_body_commits_prologue
#assert_axioms runGatedForestTurn_prologue_survives_failed_body
#assert_axioms runGatedForestTurn_committing_body
#assert_axioms runGatedForestTurn_conserves_modulo_burn

/-! ### A2 non-vacuity over the PRODUCTION path (`runGatedForestTurn`).

A committing turn (the balance-neutral `logBumpForestG` emit) with proposer 5 + treasury 6 configured
and fee 10 ⇒ on commit the agent (cell 0) net −fee, proposer +5, treasury +3, residue 2 burned. The
triple total over {0, 5, 6} drops by EXACTLY the burn (2). With proposer/treasury UNCONFIGURED the whole
fee burns (the wire default) — both are conservation-modulo-burn, NOT silent loss. -/

open Dregg2.Exec.StarbridgeGated (logBumpForestG)

/-- A2 demo pre-state: agent 0 (balance 100, nonce 0), proposer 5, treasury 6 (balance 0), all with the
`bal` asset table that lets `logBumpForestG`'s emit commit. -/
def a2State : RecChainedState :=
  { kernel :=
      { accounts := {0, 1, 5, 6}
        cell := fun c => if c = 0 then .record [("balance", .int 100), ("nonce", .int 0)]
                         else .record [("balance", .int 0)]
        caps := fun l => if l = 9 then [Dregg2.Authority.Cap.node 0] else []
        bal := fun c a => if c = 0 then (if a = 0 then 100 else if a = 1 then 7 else 0)
                          else if c = 1 then (if a = 0 then 5 else 0) else 0 }
    log := [] }

/-- A2 demo context: clock far out, head genesis-match, proposer cell 5, treasury cell 6. -/
def a2Ctx : AdmCtx :=
  { now := 0, frozen := [], storedHead := none, budget := 1000000000, proposer := some 5, treasury := some 6 }

/-- A2 demo header: agent 0, nonce 0 (matches `a2State`), fee 10, no expiry, prevReceipt genesis. -/
def a2Hdr : TurnHdr :=
  { agent := 0, nonce := 0, fee := 10, validUntil := none, prevReceipt := none,
    writeSet := [0], forestNonEmpty := true }

-- The production turn COMMITS (admission passes, the emit body commits, fee distributes):
#guard ((runGatedForestTurn a2Ctx a2Hdr a2State logBumpForestG).isSome)
-- The distribution fired: proposer 5 gained 5, treasury 6 gained 3 (the 50%/30% shares of fee 10):
#guard ((runGatedForestTurn a2Ctx a2Hdr a2State logBumpForestG).map
        (fun sf => (balOf (sf.kernel.cell 5), balOf (sf.kernel.cell 6)))) == some (5, 3)
-- The agent paid the full fee (100 − 10 = 90), nonce ticked:
#guard ((runGatedForestTurn a2Ctx a2Hdr a2State logBumpForestG).map
        (fun sf => (balOf (sf.kernel.cell 0), nonceOf (sf.kernel.cell 0)))) == some (90, 1)
-- THE A2 TEETH: the {0,5,6} triple drops by EXACTLY the burn (2), not the whole fee (10 = silent loss):
#guard ((runGatedForestTurn a2Ctx a2Hdr a2State logBumpForestG).map
        (fun sf => feeTriSum sf 0 5 6)) == some 98  --  100 → 98 (−2 burn)
#guard (feeTriSum a2State 0 5 6 == 100)
-- TAMPER: the WRONG "fully conserved" claim (triple unchanged = 100) is FALSE — the burn is real:
#guard (((runGatedForestTurn a2Ctx a2Hdr a2State logBumpForestG).map
        (fun sf => feeTriSum sf 0 5 6)) == some 100) == false  --  false (burn ≠ 0)
-- ...and the OLD broken behavior (whole fee silently gone, triple = 90) is ALSO FALSE — fee distributes:
#guard (((runGatedForestTurn a2Ctx a2Hdr a2State logBumpForestG).map
        (fun sf => feeTriSum sf 0 5 6)) == some 90) == false  --  false (proposer/treasury credited)

end Dregg2.Exec.TurnAdmission